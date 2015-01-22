/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

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

#include <algorithm>
#include <functional>
#include <initializer_list>
#include <list>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "opensmt/egraph/Enode.h"
#include "ibex/ibex.h"
#include "capd/capdlib.h"
#include "util/box.h"
#include "util/string.h"
#include "util/flow.h"
#include "util/logging.h"
#include "util/ibex_enode.h"
#include "util/constraint.h"
#include "util/contractor.h"

using std::function;
using std::initializer_list;
using std::list;
using std::string;
using std::unordered_set;
using std::vector;

namespace dreal {

list<capd::interval> split(capd::interval const & i, unsigned n) {
    list<capd::interval> ret;
    double lb = i.leftBound();
    double const rb = i.rightBound();
    double const width = rb - lb;
    double const step = width / n;
    for (unsigned i = 0; i < n - 1; i++) {
        ret.emplace_back(lb, min(lb + step, rb));
        lb += step;
    }
    if (lb < rb) {
        ret.emplace_back(lb, rb);
    }
    return ret;
}

bool contain_nan(capd::IVector const & v) {
    for (capd::interval const & i : v) {
        if (std::isnan(i.leftBound()) || std::isnan(i.rightBound())) {
            DREAL_LOG_INFO << "NaN Found: " << v;
            return true;
        }
    }
    return false;
}

string subst(Enode const * const e, unordered_map<string, string> subst_map) {
    string ret;
    if (e->isSymb()) {
        if (e->isTerm() && e->getPolarity() == l_False) {
            switch (e->getId()) {
            case ENODE_ID_LEQ:
                return ">";
            case ENODE_ID_LT:
                return ">=";
            case ENODE_ID_GEQ:
                return "<";
            case ENODE_ID_GT:
                return "<=";
            }
        }
        string const & name = e->getName();
        auto it = subst_map.find(name);
        if (it == subst_map.end()) {
            return name;
        } else {
            // std::cerr << "Subst! " << name << " => " << it->second << std::endl;
            return it->second;
        }
    } else if (e->isNumb()) {
        string const & name = e->getName();
        return name;
        // }
    } else if (e->isTerm()) {
        // output "("
        if (!e->getCdr()->isEnil() && (e->isPlus() || e->isMinus() || e->isTimes() || e->isPow())) {
            ret = "(";
        }
        // !(X = Y) ==> (0 = 0)
        if (e->isEq() && e->getPolarity()  == l_False) {
            ret += "0 = 0";
        } else if (e->isPlus() || e->isMinus() || e->isTimes() || e->isDiv() || e->isEq() || e->isLeq() || e->isGeq() || e->isLt() || e->isGt()) {
            // assert(getArity() == 2);
            Enode * const op = e->getCar();
            Enode * p = e->getCdr();
            // Print 1st argument
            ret += subst(p->getCar(), subst_map);
            p = p->getCdr();
            while (!p->isEnil()) {
                // output operator
                ret += subst(op, subst_map);
                // output argument
                ret += subst(p->getCar(), subst_map);
                // move p
                p = p->getCdr();
            }
        } else if (e->isPow()) {
            Enode * const op = e->getCar();
            Enode * p = e->getCdr();
            // Print 1st argument
            ret += subst(p->getCar(), subst_map);
            p = p->getCdr();
            while (!p->isEnil()) {
                // output operator
                ret += subst(op, subst_map);
                // output argument
                ret += "(";
                ret += subst(p->getCar(), subst_map);
                ret += ")";
                // move p
                p = p->getCdr();
            }
        } else if (e->isAtan2()) {
            assert(e->getArity() == 2);
            // output operator
            ret += subst(e->getCar(), subst_map);
            ret += "(";
            // output 1st argument
            ret += subst(e->getCdr()->getCar(), subst_map);
            ret += ", ";
            // output 1st argument
            ret += subst(e->getCdr()->getCdr()->getCar(), subst_map);
            ret += ")";
        } else if (e->isAcos() || e->isAsin() || e->isAtan() || e->isMatan() || e->isSafeSqrt() ||
                   e->isSin() || e->isCos() || e->isTan() || e->isLog() || e->isExp() || e->isSinh() || e->isCosh() || e->isTanh() || e->isAbs()) {
            assert(e->getArity() == 1);
            // output operator
            ret += subst(e->getCar(), subst_map);
            ret += "(";
            // output 1st argument
            ret += subst(e->getCdr()->getCar(), subst_map);
            ret += ")";
        } else {
            ret += subst(e->getCar(), subst_map);
            Enode * p = e->getCdr();
            while (!p->isEnil()) {
                ret += " ";
                // print Car
                ret += subst(p->getCar(), subst_map);
                p = p->getCdr();
            }
        }
        // output ")"
        if (!e->getCdr()->isEnil() && (e->isPlus() || e->isMinus() || e->isTimes() || e->isPow())) {
            ret += ")";
        }
    } else if (e->isList()) {
        if (e->isEnil()) {
            ret += "-";
        } else {
            ret += "[";
            ret += subst(e->getCar(), subst_map);
            Enode * p = e->getCdr();
            while (!p->isEnil()) {
                ret += ", ";
                ret += subst(p->getCar(), subst_map);
                p = p->getCdr();
            }
            ret += "]";
        }
    } else if (e->isDef()) {
        throw std::logic_error("unreachable");
    } else if (e->isEnil()) {
        throw std::logic_error("unreachable");
    } else {
        throw std::logic_error("unreachable");
    }
    return ret;
}

// Build CAPD string from integral constraint
// example : "var:v_2_0, x_2_0;fun:(-9.8000000000000007+(-0.450000*v_2_0)), v_2_0;"
string build_capd_string(integral_constraint const & ic) {
    // Collect _0 variables
    vector<Enode *> const & vars_0 = ic.get_vars_0();
    vector<string> vars_0_strs;
    for (Enode * const var_0 : vars_0) {
        vars_0_strs.push_back(var_0->getCar()->getName());
    }
    string diff_var = "var:" + join(vars_0_strs, ", ") + ";";
    flow const & _flow = ic.get_flow();
    vector<string> params_strs = _flow.get_vars();

    // Build Map
    unordered_map<string, string> subst_map;
    for (unsigned i = 0; i < vars_0.size(); i++) {
        string const & from = params_strs[i];
        string const & to   = vars_0[i]->getCar()->getName();
        subst_map.emplace(from, to);
        DREAL_LOG_INFO << "Subst Map: " << from << " -> " << to;
    }

    // Call Subst, and collect strings
    vector<string> ode_strs;
    for (Enode * const ode : _flow.get_odes()) {
        // std::cerr << "Before subst: " << ode << std::endl;
        ode_strs.push_back(subst(ode, subst_map));
    }
    string diff_fun = "fun:" + join(ode_strs, ", ") + ";";
    return diff_var + diff_fun;
}

capd::IVector extract_ivector(box const & b, std::vector<Enode *> const & vars) {
    capd::IVector intvs(vars.size());
    for (unsigned i = 0; i < vars.size(); i++) {
        Enode * const var = vars[i];
        ibex::Interval const & intv = b[var];
        intvs[i] = capd::interval(intv.lb(), intv.ub());
    }
    return intvs;
}

void update_box_with_ivector(box & b, std::vector<Enode *> const & vars, capd::IVector iv) {
    capd::IVector intvs(vars.size());
    for (unsigned i = 0; i < vars.size(); i++) {
        b[vars[i]] = ibex::Interval(iv[i].leftBound(), iv[i].rightBound());
    }
    return;
}
contractor_capd_fwd_simple::contractor_capd_fwd_simple(box const & /* box */, ode_constraint const * const ctr)
    : contractor_cell(contractor_kind::CAPD_FWD), m_ctr(ctr) {
}

box contractor_capd_fwd_simple::prune(box b) const {
    // TODO(soonhok): implement this
    return b;
}
// ode_solver::ODE_result ode_solver::simple_ODE_forward(IVector const & X_0, IVector & X_t, interval const & T,
//                                                       IVector const & inv, vector<IFunction> & funcs) {
//     bool prune_params_result = prune_params();
//     if (!prune_params_result) {
//         return ODE_result::UNSAT;
//     }

//     // X_t = X_t \cup (X_0 + (d/dt Inv) * T)
//     for (unsigned i = 0; i < X_0.dimension(); i++) {
//         interval const & x_0 = X_0[i];
//         interval & x_t = X_t[i];
//         IFunction & dxdt = funcs[i];
//         set_params(dxdt);
//         try {
//             interval new_x_t = x_0 + dxdt(inv) * T;
//             if (!intersection(new_x_t, x_t, x_t)) {
//                 DREAL_LOG_INFO << "ode_solver::simple_ODE_forward: no intersection for X_T => UNSAT";
//                 return ODE_result::UNSAT;
//             }
//         } catch (exception& e) {
//             DREAL_LOG_FATAL << "ode_solver::simple_ODE_forward: Exception in Simple_ODE: " << e.what();
//         }
//     }
//     // update
//     IVector_to_varlist(X_t, m_t_vars);
//     return ODE_result::SAT;
// }

contractor_capd_fwd_full::contractor_capd_fwd_full(box const & /* box */, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size)
    : contractor_cell(contractor_kind::CAPD_FWD), m_ctr(ctr), m_taylor_order(taylor_order), m_grid_size(grid_size) {
}

bool contractor_capd_fwd_full::inner_loop(capd::IOdeSolver & solver, capd::interval const & prevTime, capd::interval const T, vector<pair<capd::interval, capd::IVector>> & enclosures) const {
    DREAL_LOG_INFO << "contractor_capd_fwd_full::inner_loop";

    capd::interval const stepMade = solver.getStep();
    capd::IOdeSolver::SolutionCurve const & curve = solver.getCurve();
    capd::interval domain = capd::interval(0, 1) * stepMade;
    list<capd::interval> intvs;
    if (prevTime.rightBound() < T.leftBound()) {
        capd::interval pre_T = capd::interval(0, T.leftBound() - prevTime.rightBound());
        domain.setLeftBound(T.leftBound() - prevTime.rightBound());
        intvs = split(domain, m_grid_size);
        intvs.push_front(pre_T);
    } else {
        intvs = split(domain, m_grid_size);
    }

    for (capd::interval const & subsetOfDomain : intvs) {
        capd::interval dt = prevTime + subsetOfDomain;
        capd::IVector v = curve(subsetOfDomain);
        // if (!check_invariant(v, m_inv)) {
        //     // TODO(soonhok): invariant
        //     return true;
        // }
        DREAL_LOG_INFO << "contractor_capd_fwd_full::inner_loop:" << dt << "\t" << v;
        if (prevTime + subsetOfDomain.rightBound() > T.leftBound()) {
            enclosures.emplace_back(dt, v);
        }
        // // TODO(soonhok): visualization
        // if (m_config.nra_json) {
        //     m_trajectory.emplace_back(prevTime + subsetOfDomain, v);
        // }
    }
    return false;
}

bool contractor_capd_fwd_full::prune(vector<pair<capd::interval, capd::IVector>> & enclosures, capd::IVector & X_t, capd::interval & T) const {
    // 1) Intersect each v in enclosure with X_t.
    // 2) If there is no intersection in 1), set dt an empty interval [0, 0]
    for (pair<capd::interval, capd::IVector> & item : enclosures) {
        capd::interval & dt = item.first;
        capd::IVector &  v  = item.second;
        // v = v union X_t
        if (!intersection(v, X_t, v)) {
            dt.setLeftBound(0.0);
            dt.setRightBound(0.0);
        }
    }
    enclosures.erase(remove_if(enclosures.begin(), enclosures.end(),
                            [](pair<capd::interval, capd::IVector> const & item) {
                                capd::interval const & dt = item.first;
                                return dt.leftBound() == 0.0 && dt.rightBound() == 0.0;
                            }),
                 enclosures.end());
    if (enclosures.empty()) {
        return false;
    } else {
        T = enclosures.begin()->first;
        X_t  = enclosures.begin()->second;
        for (pair<capd::interval, capd::IVector> & item : enclosures) {
            capd::interval & dt = item.first;
            capd::IVector &  v  = item.second;
            X_t  = intervalHull(X_t,  v);
            T    = intervalHull(T, dt);
        }
        return true;
    }
}

box contractor_capd_fwd_full::prune(box b) const {
    m_used_constraints.insert(m_ctr);
    DREAL_LOG_INFO << "contractor_capd_fwd_full::prune";
    integral_constraint const & ic = m_ctr->get_ic();
    string const & capd_str = build_capd_string(ic);
    capd::IVector X_0 = extract_ivector(b, ic.get_vars_0());
    capd::IVector X_t = extract_ivector(b, ic.get_vars_t());
    // TODO(soonhok): Here we still assume that time_0 = zero.
    ibex::Interval const & ibex_T = b[ic.get_time_t()];
    capd::interval T(ibex_T.lb(), ibex_T.ub());
    DREAL_LOG_INFO << "contractor_capd_fwd_full: diff sys = " << capd_str;
    DREAL_LOG_INFO << "X_0 : " << X_0;
    DREAL_LOG_INFO << "X_t : " << X_t;
    DREAL_LOG_INFO << "T   : " << T;
    capd::IMap vectorField(capd_str);

    // set_params(vectorField);
    capd::IOdeSolver solver(vectorField, m_taylor_order);
    capd::ITimeMap timeMap(solver);
    capd::C0Rect2Set s(X_0);
    timeMap.stopAfterStep(true);
    capd::interval prevTime(0.);

    vector<pair<capd::interval, capd::IVector>> enclosures;
    do {
        // Move s toward m_T.rightBound()
        timeMap(T.rightBound(), s);
        if (contain_nan(s)) {
            DREAL_LOG_INFO << "ode_solver::compute_forward: contain NaN";
        }

        if (T.leftBound() <= timeMap.getCurrentTime().rightBound()) {
            //                     [     T      ]
            // [     current Time     ]
            bool invariantViolated = inner_loop(solver, prevTime, T, enclosures);
            if (invariantViolated) {
                // TODO(soonhok): invariant
                DREAL_LOG_INFO << "ode_solver::compute_forward: invariant violated";
                // ret = ODE_result::SAT;
                break;
            }
        }
        prevTime = timeMap.getCurrentTime();
    } while (/*!invariantViolated &&*/ !timeMap.completed());
    if (prune(enclosures, X_t, T)) {
        // SAT
        update_box_with_ivector(b, ic.get_vars_t(), X_t);
        // TODO(soonhok): Here we still assume that time_0 = zero.
        b[ic.get_time_t()] = ibex::Interval(T.leftBound(), T.rightBound());
    } else {
        // UNSAT
        b.set_empty();
    }
    DREAL_LOG_INFO << "X_0 : " << X_0;
    DREAL_LOG_INFO << "X_t : " << X_t;
    DREAL_LOG_INFO << "T   : " << T;
    return b;
}

contractor_capd_bwd_simple::contractor_capd_bwd_simple(box const & /* box */, ode_constraint const * const ctr)
    : contractor_cell(contractor_kind::CAPD_FWD), m_ctr(ctr) {
}

box contractor_capd_bwd_simple::prune(box b) const {
    // TODO(soonhok): implement this
    return b;
}

contractor_capd_bwd_full::contractor_capd_bwd_full(box const & /*box*/, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size)
    : contractor_cell(contractor_kind::CAPD_BWD), m_ctr(ctr), m_taylor_order(taylor_order), m_grid_size(grid_size) {
}
box contractor_capd_bwd_full::prune(box b) const {
    // TODO(soonhok): implement this
    DREAL_LOG_INFO << "contractor_capd_bwd_full::prune";
    DREAL_LOG_INFO << *m_ctr;
    return b;
}

contractor mk_contractor_capd_fwd_simple(box const & box, ode_constraint const * const ctr) {
    return contractor(shared_ptr<contractor_cell>(new contractor_capd_fwd_simple(box, ctr)));
}
contractor mk_contractor_capd_fwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size) {
    return contractor(shared_ptr<contractor_cell>(new contractor_capd_fwd_full(box, ctr, taylor_order, grid_size)));
}
contractor mk_contractor_capd_bwd_simple(box const & box, ode_constraint const * const ctr) {
    return contractor(shared_ptr<contractor_cell>(new contractor_capd_bwd_simple(box, ctr)));
}
contractor mk_contractor_capd_bwd_full(box const & box, ode_constraint const * const ctr, unsigned const taylor_order, unsigned const grid_size) {
    return contractor(shared_ptr<contractor_cell>(new contractor_capd_bwd_full(box, ctr, taylor_order, grid_size)));
}
}  // namespace dreal
