/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "dsolvers/nra_solver.h"
#include <algorithm>
#include <exception>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>
#include "./config.h"
#include "ibex/ibex.h"
#include "util/box.h"
#include "constraint/constraint.h"
#include "contractor/contractor.h"
#include "util/ibex_enode.h"
#include "util/logging.h"
#include "icp/icp.h"
#include "util/stat.h"
#include "json/json.hpp"
#include "util/proof.h"
#include "interpolation/tilingInterpolation.h"
#include "interpolation/interpolationUtils.h"

using ibex::IntervalVector;
using nlohmann::json;
using std::all_of;
using std::boolalpha;
using std::cerr;
using std::cout;
using std::endl;
using std::get;
using std::logic_error;
using std::make_pair;
using std::map;
using std::numeric_limits;
using std::ofstream;
using std::pair;
using std::runtime_error;
using std::sort;
using std::string;
using std::unique_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {
nra_solver::nra_solver(const int i, const char * n, SMTConfig & c, Egraph & e, SStore & t,
                       vector<Enode *> & x, vector<Enode *> & d, vector<Enode *> & s)
    : OrdinaryTSolver(i, n, c, e, t, x, d, s), m_box(vector<Enode*>({})) {
    if (c.nra_precision == 0.0) c.nra_precision = 0.001;
}

nra_solver::~nra_solver() {
    DREAL_LOG_INFO << "~nra_solver()";
    if (config.nra_use_stat) {
        cout << config.nra_stat << endl;
    }
}

// `inform` sets up env (mapping from variables(enode) in literals to their [lb, ub])
lbool nra_solver::inform(Enode * e) {
    DREAL_LOG_INFO << "nra_solver::inform: " << e;
    // Collect Literal
    m_lits.push_back(e);
    m_need_init = true;
    return l_Undef;
}

// Asserts a literal into the solver. If by chance you are able to
// discover inconsistency you may return false. The real consistency
// state will be checked with "check" assertLit adds a literal(e) to
// stack of asserted literals.
bool nra_solver::assertLit(Enode * e, bool reason) {
    DREAL_LOG_INFO << "nra_solver::assertLit: " << e
                   << ", reason: " << boolalpha << reason
                   << ", polarity: " << e->getPolarity().toInt()
                   << ", deduced: " << e->isDeduced()
                   << ", getDeduced: " << e->getDeduced().toInt()
                   << ", getIndex: " << e->getDedIndex()
                   << ", level: " << m_stack.size()
                   << ", ded.size = " << deductions.size();

    if (config.nra_use_stat) { config.nra_stat.increase_assert(); }

    if (m_need_init) {
        initialize(m_lits);
        m_need_init = false;
    }

    (void)reason;
    assert(e);
    assert(belongsToT(e));
    assert(e->hasPolarity());
    assert(e->getPolarity() == l_False || e->getPolarity() == l_True);
    if (e->isDeduced() && e->getPolarity() == e->getDeduced() && e->getDedIndex() == id) {
        DREAL_LOG_INFO << "nra_solver::assertLit: " << e << " is deduced";
        return true;
    }
    auto it = m_ctr_map.find(make_pair(e, e->getPolarity() == l_True));
    if (it != m_ctr_map.end()) {
        m_stack.push_back(it->second.get());
    } else if (e->isForallT()) {
        // TODO(soonhok): implement this
        return true;
    } else if (e->isIntegral() && e->getPolarity() == l_False) {
        return true;
    } else {
        DREAL_LOG_FATAL << "Unknown literal "
                        << (e->getPolarity() == l_False ? "!" : "")
                        << e << " is asserted";
        throw logic_error("unknown literal is asserted");
    }
    return true;
}

// Update ctr_map by adding new nonlinear_constraints
void initialize_nonlinear_constraints(map<pair<Enode*, bool>, unique_ptr<constraint>> & ctr_map,
                                      vector<Enode *> const & lits) {
    // 1. Collect all variables (Enode *) in literals
    unordered_set<Enode *> var_set;
    for (Enode * const l : lits) {
        unordered_set<Enode *> const & vars = l->get_vars();
        var_set.insert(vars.begin(), vars.end());
    }

    // 2. Create Nonlinear constraints.
    for (Enode * const l : lits) {
        auto it_nc_pos = ctr_map.find(make_pair(l, true));
        auto it_nc_neg = ctr_map.find(make_pair(l, false));
        if (it_nc_pos == ctr_map.end()) {
            unique_ptr<constraint> nc_pos(new nonlinear_constraint(l, var_set, l_True));
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect NonlinearConstraint (+): " << *nc_pos;
            ctr_map.emplace(make_pair(l, true),  move(nc_pos));
        }
        if (it_nc_neg == ctr_map.end()) {
            unique_ptr<constraint> nc_neg(new nonlinear_constraint(l, var_set, l_False));
            DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect NonlinearConstraint (-): " << *nc_neg;
            ctr_map.emplace(make_pair(l, false), move(nc_neg));
        }
    }
}

// Update ctr_map by adding new ode constraints, from the information collected in ints and invs
void initialize_ode_constraints(map<pair<Enode*, bool>, unique_ptr<constraint>> & ctr_map,
                                vector<integral_constraint> const & ints,
                                vector<forallt_constraint> const & invs) {
    // Attach the corresponding forallT literals to integrals
    for (integral_constraint ic : ints) {
        vector<forallt_constraint> local_invs;
        for (forallt_constraint fc : invs) {
            // Link ForallTConstraint fc with IntegralConstraint ic, if
            //    fc.flow == ic.flow
            //    vars(fc.inv) \subseteq ic.vars_t
            if (fc.get_flow_id() == ic.get_flow_id()) {
                unordered_set<Enode *> vars_in_fc = fc.get_inv()->get_vars();
                bool const included = all_of(vars_in_fc.begin(), vars_in_fc.end(),
                                             [&ic](Enode const * var_in_fc) {
                                                 vector<Enode *> const & vars_t_in_ic = ic.get_vars_t();
                                                 return find(vars_t_in_ic.begin(), vars_t_in_ic.end(), var_in_fc) != vars_t_in_ic.end();
                                             });
                if (included) {
                    local_invs.push_back(fc);
                }
            }
        }
        unique_ptr<constraint> oc(new ode_constraint(ic, local_invs));
        DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect ODEConstraint: " << *oc;
        ctr_map.emplace(make_pair(ic.get_enode(), true), move(oc));
    }
}

// Given a list of theory literals (vector<Enode *>)
// build a mapping from Enode to constraint (m_ctr_map)
void nra_solver::initialize_constraints(vector<Enode *> const & lits) {
    vector<integral_constraint> ints;
    vector<forallt_constraint> invs;
    vector<Enode *> nonlinear_lits;
    for (Enode * l : lits) {
        // Partition ODE-related constraint into integrals and forallTs
        if (l->isIntegral()) {
            integral_constraint ic = mk_integral_constraint(l, egraph.flow_maps);
            ints.push_back(ic);
        } else if (l->isForall()) {
            // Collect Generic Forall constraints.
            auto it_fc_pos = m_ctr_map.find(make_pair(l, true));
            auto it_fc_neg = m_ctr_map.find(make_pair(l, false));
            if (it_fc_pos == m_ctr_map.end()) {
                unique_ptr<constraint> fc_pos(new generic_forall_constraint(l, l_True));
                DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect GenericForallConstraint (+): " << *fc_pos;
                m_ctr_map.emplace(make_pair(l, true), move(fc_pos));
            }
            if (it_fc_neg == m_ctr_map.end()) {
                unique_ptr<constraint> fc_neg (new generic_forall_constraint(l, l_False));
                DREAL_LOG_INFO << "nra_solver::initialize_constraints: collect GenericForallConstraint (-): " << *fc_neg;
                m_ctr_map.emplace(make_pair(l, false), move(fc_neg));
            }
        } else if (l->isForallT()) {
            forallt_constraint fc = mk_forallt_constraint(l);
            invs.push_back(fc);
        } else if (l->get_forall_vars().empty()) {
            nonlinear_lits.push_back(l);
        } else {
            DREAL_LOG_FATAL << "nra_solver::initialize_constraints: No Patten";
            throw runtime_error("nra_solver::initialize_constraints: No Patten");
        }
    }
    initialize_ode_constraints(m_ctr_map, ints, invs);
    initialize_nonlinear_constraints(m_ctr_map, nonlinear_lits);
}

contractor build_contractor(box const & box, scoped_vec<constraint *> const &ctrs, bool const complete, SMTConfig & config) {
    vector<nonlinear_constraint const *> nl_ctrs;
    vector<contractor> nl_ctcs;
    nl_ctcs.reserve(ctrs.size());
    vector<contractor> nl_eval_ctcs;
    nl_eval_ctcs.reserve(ctrs.size());
    vector<contractor> ode_ctcs;
    ode_ctcs.reserve(ctrs.size());
    vector<contractor> forall_ctcs;
    forall_ctcs.reserve(ctrs.size());
    vector<contractor> generic_forall_ctcs;
    generic_forall_ctcs.reserve(ctrs.size());
    // Add contractor_sample if --sample option is used
    if (config.nra_sample > 0 && complete) {
        nl_ctcs.push_back(mk_contractor_sample(config.nra_sample, ctrs.get_vec()));
    }
    for (constraint * const ctr : ctrs.get_reverse()) {
        switch (ctr->get_type()) {
        case constraint_type::Nonlinear: {
            nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
            if (!nl_ctr->is_neq()) {
                nl_ctcs.push_back(mk_contractor_ibex_fwdbwd(box, nl_ctr));
                nl_ctrs.push_back(nl_ctr);
            } else {
                // Case: != (not equal), do nothing
            }
            nl_eval_ctcs.push_back(mk_contractor_eval(box, nl_ctr));
            break;
        }
#ifdef SUPPORT_ODE
        case constraint_type::ODE: {
            // TODO(soonhok): add heuristics to choose fwd/bwd
            if (complete) {
                ode_ctcs.emplace_back(
                    mk_contractor_try(
                        mk_contractor_capd_fwd_full(box, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size)));
                if (!config.nra_ODE_forward_only) {
                    ode_ctcs.emplace_back(
                        mk_contractor_try(
                            mk_contractor_capd_bwd_full(box, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size)));
                }
            }
            break;
        }
#endif
        case constraint_type::GenericForall: {
            generic_forall_constraint const * const generic_forall_ctr = dynamic_cast<generic_forall_constraint *>(ctr);
            generic_forall_ctcs.push_back(mk_contractor_generic_forall(box, generic_forall_ctr));
            break;
        }
        default:
            DREAL_LOG_FATAL << "Unknown Constraint Type: " << ctr->get_type() << " " <<  *ctr << endl;
        }
    }
    if (config.nra_polytope) {
        nl_ctcs.push_back(mk_contractor_ibex_polytope(config.nra_precision, box.get_vars(), nl_ctrs));
    }
    nl_ctcs.push_back(mk_contractor_int());
    // Add contractor_sample if --sample option is used
    if (config.nra_aggressive > 0 && complete) {
        nl_ctcs.push_back(mk_contractor_sample(config.nra_aggressive, ctrs.get_vec()));
    }

    auto term_cond = [](dreal::box const & old_box, dreal::box const & new_box) {
        double const threshold = 0.01;
        // If there is a dimension which is improved more than
        // threshold, we stop the current fixed-point computation.
        for (unsigned i = 0; i < old_box.size(); i++) {
            double const new_box_i = new_box[i].diam();
            double const old_box_i = old_box[i].diam();
            if (new_box_i == numeric_limits<double>::infinity()) {
                continue;
            }
            if (old_box_i == 0) {
                // The i-th dimension was already a point, nothing to improve.
                continue;
            }
            double const improvement = 1 - new_box_i / old_box_i;
            assert(!std::isnan(improvement));
            if (improvement >= threshold) {
                return false;
            }
        }
        return true;
    };
    if (complete && ode_ctcs.size() > 0) {
        return mk_contractor_fixpoint(term_cond,
                                      {nl_ctcs, forall_ctcs, generic_forall_ctcs, ode_ctcs, nl_eval_ctcs});
    } else {
        return mk_contractor_fixpoint(term_cond,
                                      {nl_ctcs, forall_ctcs, generic_forall_ctcs, nl_eval_ctcs});
    }
}

void nra_solver::initialize(vector<Enode *> const & lits) {
    m_box.constructFromLiterals(lits);
    initialize_constraints(lits);
}


// Saves a backtrack point You are supposed to keep track of the
// operations, for instance in a vector called "undo_stack_term", as
// happens in EgraphSolver
void nra_solver::pushBacktrackPoint() {
    DREAL_LOG_INFO << "nra_solver::pushBacktrackPoint " << m_stack.size();
    if (m_need_init) {
        initialize(m_lits);
        m_need_init = false;
    }
    if (config.nra_use_stat) { config.nra_stat.increase_push(); }
    m_stack.push();
    m_used_constraint_vec.push();
    m_boxes.push_back(m_box);
    m_boxes.push();
}

// Restore a previous state. You can now retrieve the size of the
// stack when you pushed the last backtrack point. You have to
// implement the necessary backtrack operations (see for instance
// backtrackToStackSize() in EgraphSolver) Also make sure you clean
// the deductions you did not communicate
void nra_solver::popBacktrackPoint() {
    if (config.nra_use_stat) { config.nra_stat.increase_pop(); }
    DREAL_LOG_INFO << "nra_solver::popBacktrackPoint\t m_stack.size()      = " << m_stack.size();
    m_boxes.pop();
    m_box = m_boxes.last();
    m_used_constraint_vec.pop();
    m_stack.pop();
}

void nra_solver::handle_sat_case(box const & b) const {
    // SAT
    // --proof option
    if (config.nra_proof) {
        config.nra_proof_out.close();
        config.nra_proof_out.open(config.nra_proof_out_name.c_str(), ofstream::out | ofstream::trunc);
        display(config.nra_proof_out, b, !config.nra_readable_proof, true);
    }
    // --interpolant option
    if (config.nra_interpolant) {
        delete interpolator;
        interpolator = NULL;
    }
    // --model option
    if (config.nra_model && config.nra_multiple_soln == 1) {
        // Only output here when --multiple_soln is not used
        output_solution(b, config);
    }
#ifdef SUPPORT_ODE
    // --visualize option
    if (config.nra_json) {
        json traces = {};
        // Need to run ODE pruning operator once again to generate a trace
        for (constraint * const ctr : m_stack) {
            if (ctr->get_type() == constraint_type::ODE) {
                contractor_capd_fwd_full fwd_full(b, dynamic_cast<ode_constraint *>(ctr), config.nra_ODE_taylor_order, config.nra_ODE_grid_size);
                json trace = fwd_full.generate_trace(b, config);
                traces.push_back(trace);
            }
        }
        json vis_json;
        vis_json["traces"] = traces;
        config.nra_json_out << vis_json.dump() << endl;;
    }
#endif
    // For API call
    b.assign_to_enode();
    return;
}

void nra_solver::handle_deduction() {
    for (Enode * const l : m_lits) {
        if (l->getPolarity() == l_Undef && !l->isDeduced()) {
            auto it = m_ctr_map.find(make_pair(l, true));
            if (it != m_ctr_map.end()) {
                constraint * ctr = it->second.get();
                nonlinear_constraint const * const nl_ctr = dynamic_cast<nonlinear_constraint *>(ctr);
                if (nl_ctr) {
                    pair<lbool, ibex::Interval> p = nl_ctr->eval(m_box);
                    if (p.first == l_False) {
                        // We know that this literal has to be false;
                        l->setDeduced(l_False, id);
                        deductions.push_back(l);
                        DREAL_LOG_INFO << "Deduced: " << *nl_ctr << "\t" << p.first << "\t" << p.second;
                    } else if (p.first == l_True) {
                        // We know that this literal has to be true;
                        l->setDeduced(l_True, id);
                        deductions.push_back(l);
                        DREAL_LOG_INFO << "Deduced: " << *nl_ctr << "\t" << p.first << "\t" << p.second;
                    }
                }
            }
        }
    }
}

// Check for consistency.
// If flag is set make sure you run a complete check
bool nra_solver::check(bool complete) {
    if (config.nra_use_stat) { config.nra_stat.increase_check(complete); }
    if (m_stack.size() == 0) { return true; }
    DREAL_LOG_INFO << "nra_solver::check(complete = " << boolalpha << complete << ")"
                   << "stack size = " << m_stack.size();
    m_ctc = build_contractor(m_box, m_stack, complete, config);
    // initialize the proof
    if (config.nra_proof) {
         output_start(config.nra_proof_out, m_box, config.nra_readable_proof);
    }
    // initialize the interpolant
    if (config.nra_interpolant) {
        std::vector<constraint const *> cstrs(m_stack.size());
        int i = 0;
        for (constraint const * ptr: m_stack) {
          cstrs[i] = ptr;
          i++;
        }
        auto a_b_cstr = splitAB(cstrs);
        auto a_cstrs = get<0>(a_b_cstr);
        auto b_cstrs = get<1>(a_b_cstr);
        DREAL_LOG_INFO << "a_cstrs: " << a_cstrs.size();
        DREAL_LOG_INFO << "b_cstrs: " << b_cstrs.size();
        interpolator = new tilingInterpolation(m_box, a_cstrs, b_cstrs);
    }
    if (complete) {
        //TODO setup the proof and the interpolant
        // Complete Check ==> Run ICP
        if (config.nra_ncbt) {
            m_box = ncbt_icp::solve(m_box, m_ctc, config);
        } else if (config.nra_parallel) {
            m_box = parallel_icp::solve(m_box, m_ctc, config);
        } else {
            m_box = naive_icp::solve(m_box, m_ctc, config);
        }
    } else {
        // Incomplete Check ==> Prune Only
        try {
            m_ctc.prune(m_box, config);
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
    }
    bool result = !m_box.is_empty();
    DREAL_LOG_INFO << "nra_solver::check: result = " << boolalpha << result;
    for (constraint const * ctr : m_ctc.used_constraints()) {
        m_used_constraint_vec.push_back(ctr);
    }
    if (!result) {
        explanation = generate_explanation(m_used_constraint_vec);
        if (config.nra_interpolant) {
            Enode * itp = interpolator->get_interpolant();
            std::cout << "interpolant" << std::endl;
            itp->print(std::cout);
            std::cout << std::endl;
        }
    } else {
        if (!complete && config.sat_theory_propagation) {
            handle_deduction();
        }
        if (complete) {
            handle_sat_case(m_box);
        }
    }
    DREAL_LOG_DEBUG << "nra_solver::check(" << (complete ? "complete" : "incomplete") << ") = " << result;
    return result;
}

vector<Enode *> nra_solver::generate_explanation(scoped_vec<constraint const *> const & ctr_vec) {
    unordered_set<Enode *> bag;
    for (constraint const * ctr : ctr_vec) {
        vector<Enode *> const & enodes_in_ctr = ctr->get_enodes();
        for (Enode * const e : enodes_in_ctr) {
            if (e->hasPolarity()) {
                bag.insert(e);
            }
        }
    }
    vector<Enode *> exps;
    copy(bag.begin(), bag.end(), back_inserter(exps));
    sort(exps.begin(), exps.end(), [](Enode const * const e1, Enode const * const e2) {
            return e1->getId() < e2->getId();
        });
    return exps;
}

// Return true if the enode belongs to this theory. You should examine
// the structure of the node to see if it matches the theory operators
bool nra_solver::belongsToT(Enode * e) {
    (void)e;
    assert(e);
    return true;
}

// Copy the model into enode's data
void nra_solver::computeModel() {
    DREAL_LOG_DEBUG << "nra_solver::computeModel" << endl;
}
}  // namespace dreal
