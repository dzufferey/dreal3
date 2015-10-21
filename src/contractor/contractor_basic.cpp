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

#include <algorithm>
#include <chrono>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "constraint/constraint.h"
#include "contractor/contractor_basic.h"
#include "ibex/ibex.h"
#include "opensmt/egraph/Enode.h"
#include "util/box.h"
#include "util/logging.h"
#include "util/proof.h"
#include "interpolation/tilingInterpolation.h"
#include "util/interruptible_thread.h"

using std::back_inserter;
using std::cerr;
using std::cout;
using std::dynamic_pointer_cast;
using std::endl;
using std::function;
using std::initializer_list;
using std::make_pair;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::queue;
using std::set;
using std::shared_ptr;
using std::unordered_map;
using std::unordered_set;
using std::vector;

namespace dreal {
ostream & operator<<(ostream & out, contractor_cell const & c) {
    return c.display(out);
}

contractor_seq::contractor_seq(initializer_list<contractor> const & l)
    : contractor_cell(contractor_kind::SEQ), m_vec(l) { }
contractor_seq::contractor_seq(vector<contractor> const & v)
    : contractor_cell(contractor_kind::SEQ), m_vec(v) {
}
contractor_seq::contractor_seq(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::SEQ), m_vec(1, c1) {
    m_vec.push_back(c2);
}

void contractor_seq::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_seq::prune";
    m_input  = ibex::BitSet::empty(b.front().size()); //TODO avoid creation of new sets
    m_output = ibex::BitSet::empty(b.front().size()); //TODO avoid creation of new sets
    m_used_constraints.clear();
    for (contractor const & c : m_vec) {
        interruption_point();
        c.prune(b, config);
        m_input.union_with(c.input());
        m_output.union_with(c.output());
        unordered_set<shared_ptr<constraint>> const & used_ctrs = c.used_constraints();
        m_used_constraints.insert(used_ctrs.begin(), used_ctrs.end());
        if (b.front().is_empty()) {
            return;
        }
    }
}

ostream & contractor_seq::display(ostream & out) const {
    out << "contractor_seq(";
    for (contractor const & c : m_vec) {
        out << c << ", ";
    }
    out << ")";
    return out;
}

contractor_try::contractor_try(contractor const & c)
    : contractor_cell(contractor_kind::TRY), m_c(c) { }
void contractor_try::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_try::prune: ";
    thread_local static box old_box(b.front());
    old_box = b.front();
    try {
        m_c.prune(b, config);
    } catch (contractor_exception & e) {
        DREAL_LOG_INFO << "contractor_try: exception caught, \""
                       << e.what() << "\n";
        b.front() = old_box;
        return;
    }
    m_input  = m_c.input();
    m_output = m_c.output();
    m_used_constraints = m_c.used_constraints();
}
ostream & contractor_try::display(ostream & out) const {
    out << "contractor_try("
        << m_c << ")";
    return out;
}

contractor_try_or::contractor_try_or(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::TRY_OR), m_c1(c1), m_c2(c2) { }
void contractor_try_or::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_try_or::prune";
    thread_local static box old_box(b.front());
    old_box = b.front();
    contractor const * ctc = &m_c1;
    try {
        ctc->prune(b, config);
    } catch (contractor_exception & e) {
        b.front() = old_box;
        ctc = &m_c2;
        ctc->prune(b, config);
    }
    m_input  = ctc->input();
    m_output = ctc->output();
    m_used_constraints = ctc->used_constraints();
}
ostream & contractor_try_or::display(ostream & out) const {
    out << "contractor_try_or("
        << m_c1 << ", "
        << m_c2 << ")";
    return out;
}

contractor_throw_if_empty::contractor_throw_if_empty(contractor const & c)
    : contractor_cell(contractor_kind::THROW_IF_EMPTY), m_c(c) { }
void contractor_throw_if_empty::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_throw_if_empty::prune";
    thread_local static box old_box(b.front());
    old_box = b.front();
    m_c.prune(b, config);
    if (b.front().is_empty()) {
        b.front() = old_box;
        throw contractor_exception("throw if empty");
    } else {
        m_input  = m_c.input();
        m_output = m_c.output();
        m_used_constraints = m_c.used_constraints();
        return;
    }
}
ostream & contractor_throw_if_empty::display(ostream & out) const {
    out << "contractor_throw_if_empty(" << m_c << ")";
    return out;
}

contractor_join::contractor_join(contractor const & c1, contractor const & c2)
    : contractor_cell(contractor_kind::JOIN), m_c1(c1), m_c2(c2) { }
void contractor_join::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_join::prune";
    thread_local static box b1(b.front());
    b1 = b.front();

    // run m_c1
    m_c1.prune(b, config);
    m_input = m_c1.input();
    m_output = m_c1.output();
    m_used_constraints = m_c1.used_constraints();

    // swap
    b.swap();
    b.front() = b1;
    b1 = b.back();

    // run m_c2
    m_input.union_with(m_c2.input());
    m_output.union_with(m_c2.output());
    unordered_set<shared_ptr<constraint>> const & used_ctrs2 = m_c2.used_constraints();
    m_used_constraints.insert(used_ctrs2.begin(), used_ctrs2.end());
    m_c2.prune(b, config);

    // join(hull)
    b.front().hull(b1);
}
ostream & contractor_join::display(ostream & out) const {
    out << "contractor_join(" << m_c1 << ", " << m_c2 << ")";
    return out;
}

contractor_ite::contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else)
    : contractor_cell(contractor_kind::ITE), m_guard(guard), m_c_then(c_then), m_c_else(c_else) { }
void contractor_ite::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_ite::prune";
    contractor const * ctc = &m_c_then;
    if (!m_guard(b.front())) {
        ctc = &m_c_else;
    }
    ctc->prune(b, config);
    m_input  = ctc->input();
    m_output = ctc->output();
    m_used_constraints = ctc->used_constraints();
}
ostream & contractor_ite::display(ostream & out) const {
    out << "contractor_ite(" << m_c_then << ", " << m_c_else << ")";
    return out;
}

contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, contractor const & c)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(1, c) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<contractor> const & clist)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(clist) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, vector<contractor> const & cvec)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist(cvec) { }
contractor_fixpoint::contractor_fixpoint(function<bool(box const &, box const &)> term_cond, initializer_list<vector<contractor>> const & cvec_list)
    : contractor_cell(contractor_kind::FP), m_term_cond(term_cond), m_clist() {
    for (auto const & cvec : cvec_list) {
        m_clist.insert(m_clist.end(), cvec.begin(), cvec.end());
    }
}

void contractor_fixpoint::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_fix::prune -- begin";
    if (config.nra_worklist_fp) {
        // TODO(soonhok): worklist_fixpoint still has a problem
        worklist_fixpoint_alg(b, config);
        DREAL_LOG_DEBUG << "contractor_fix::prune -- end";
    } else {
        naive_fixpoint_alg(b, config);
        DREAL_LOG_DEBUG << "contractor_fix::prune -- end";
    }
}
ostream & contractor_fixpoint::display(ostream & out) const {
    out << "contractor_fixpoint(";
    for (contractor const & c : m_clist) {
        out << c << ", " << endl;
    }
    out << ")";
    return out;
}

void contractor_fixpoint::naive_fixpoint_alg(fbbox & b, SMTConfig & config) const {
    thread_local box old_box(b.front());
    m_input  = ibex::BitSet::empty(b.front().size());
    m_output = ibex::BitSet::empty(b.front().size());
    m_used_constraints.clear();
    // Fixed Point Loop
    do {
        interruption_point();
        old_box = b.front();
        for (contractor const & c : m_clist) {
            c.prune(b, config);
            m_input.union_with(c.input());
            m_output.union_with(c.output());
            unordered_set<shared_ptr<constraint>> const & used_constraints = c.used_constraints();
            m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
            if (b.front().is_empty()) {
                return;
            }
        }
    } while (b.front().max_diam() > config.nra_precision && !m_term_cond(old_box, b.front()));
    return;
}

void contractor_fixpoint::worklist_fixpoint_alg(fbbox & b, SMTConfig & config) const {
    thread_local static box old_box(b.front());
    m_input  = ibex::BitSet::empty(b.front().size());
    m_output = ibex::BitSet::empty(b.front().size());
    m_used_constraints.clear();

    // Add all contractors to the queue.
    unordered_set<contractor> c_set;
    queue<contractor> q;
    for (contractor const & c : m_clist) {
        if (c_set.find(c) == c_set.end()) {
            q.push(c);
            c_set.insert(c);
        }
    }
    unsigned const num_initial_ctcs = c_set.size();
    unsigned count = 0;

    // Fixed Point Loop
    do {
        interruption_point();
        old_box = b.front();
        contractor const & c = q.front();
        c.prune(b, config);
        count++;
        m_input.union_with(c.input());
        m_output.union_with(c.output());
        unordered_set<shared_ptr<constraint>> const & used_constraints = c.used_constraints();
        m_used_constraints.insert(used_constraints.begin(), used_constraints.end());
        if (b.front().is_empty()) {
            return;
        }
        c_set.erase(c);
        q.pop();

        vector<bool> diff_dims = b.front().diff_dims(old_box);
        for (unsigned i = 0; i < diff_dims.size(); i++) {
            if (diff_dims[i]) {
                for (contractor const & c : m_clist) {
                    if (c.input()[i]) {
                        if (c_set.find(c) == c_set.end()) {
                            q.push(c);
                            c_set.insert(c);
                        }
                        break;
                    }
                }
            }
        }
    } while (b.front().max_diam() > config.nra_precision && q.size() > 0 && ((count < num_initial_ctcs) || !m_term_cond(old_box, b.front())));
    return;
}


contractor_int::contractor_int() : contractor_cell(contractor_kind::INT) { }
void contractor_int::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_int::prune";

    m_input  = ibex::BitSet::empty(b.front().size());
    m_output = ibex::BitSet::empty(b.front().size());
    m_used_constraints.clear();
    unsigned i = 0;
    ibex::IntervalVector & iv = b.front().get_values();
    for (Enode * e : b.front().get_vars()) {
        if (e->hasSortInt()) {
            // ======= Proof =======
            if (config.nra_proof || config.nra_interpolant) {
                b.back() = b.front();
            }
            auto const old_iv = iv[i];
            iv[i] = ibex::integer(iv[i]);
            if (old_iv != iv[i]) {
                m_input.add(i);
                m_output.add(i);
            }
            // ======= Proof =======
            if (config.nra_proof) {
                output_pruning_step(config.nra_proof_out, b.back(), b.front(), config.nra_readable_proof, "integer pruning");
            }
            // interpolant
            if (config.nra_interpolant) {
                interpolator->integer_pruning(b.back(), b.front(), i);
            }
            if (iv[i].is_empty()) {
                // soonhok: this branch shouldn't be taken?
                b.front().set_empty();
                break;
            }
        }
        i++;
    }
}
ostream & contractor_int::display(ostream & out) const {
    out << "contractor_int()";
    return out;
}

contractor_eval::contractor_eval(shared_ptr<nonlinear_constraint> const ctr)
    : contractor_cell(contractor_kind::EVAL), m_nl_ctr(ctr) {
    // Set up input
    auto const & var_array = m_nl_ctr->get_var_array();
    for (int i = 0; i < var_array.size(); i++) {
        m_input.add(i);
    }
}

void contractor_eval::prune(fbbox & b, SMTConfig & config) const {
    DREAL_LOG_DEBUG << "contractor_eval::prune";
    //TODO DZ: check m_input
    //m_input  = ibex::BitSet::empty(b.front().size());
    m_output = ibex::BitSet::empty(b.front().size());
    pair<lbool, ibex::Interval> eval_result = m_nl_ctr->eval(b.front());
    if (eval_result.first == l_False) {
        b.back().set_empty();
        //m_input.flip();
        m_output.flip();
        m_used_constraints.insert(m_nl_ctr);
        // ======= Proof =======
        if (config.nra_proof) {
            ostringstream ss;
            Enode const * const e = m_nl_ctr->get_enode();
            ss << (e->getPolarity() == l_False ? "!" : "") << e;
            output_pruning_step(config.nra_proof_out, b.front(), b.back(), config.nra_readable_proof, ss.str());
        } 
        if (config.nra_interpolant) {
            interpolator->pruning(b.front(), b.back(), m_nl_ctr);
        }
        b.swap();
    }
}
ostream & contractor_eval::display(ostream & out) const {
    out << "contractor_eval(" << *m_nl_ctr << ")";
    return out;
}

contractor_cache::contractor_cache(contractor const & ctc)
    : contractor_cell(contractor_kind::CACHE), m_ctc(ctc) {
    // TODO(soonhok): implement this
    //
    // Need to set up:
    //
    // - ibex::BitSet m_input;
    // - ibex::BitSet m_output;
    // - std::unordered_set<constraint const *> m_used_constraints;
}

void contractor_cache::prune(fbbox & b, SMTConfig & config) const {
    // TODO(soonhok): implement this
    throw std::runtime_error("contractor_cache: not implemented yet");
    //
    // DREAL_LOG_DEBUG << "contractor_cache::prune";
    // m_input  = ibex::BitSet::empty(b.front().size());
    // m_output = ibex::BitSet::empty(b.front().size());
    // // TODO caching also require caching the proof
    // static unordered_map<box, box> cache;
    // auto const it = cache.find(b.front());
    // if (it == cache.cend()) {
    //     // Not Found
    //     m_ctc.prune(b, config);
    // } else {
    //     // Found
    //     b.front() = it->second;
    // }
}

ostream & contractor_cache::display(ostream & out) const {
    out << "contractor_cache(" << m_ctc << ")";
    return out;
}

contractor_sample::contractor_sample(unsigned const n, vector<shared_ptr<constraint>> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
    // TODO(soonhok): the following is over-approximated
}

void contractor_sample::prune(fbbox & b, SMTConfig &) const {
    DREAL_LOG_DEBUG << "contractor_sample::prune";
    m_input  = ibex::BitSet::empty(b.front().size());
    // Sample n points
    set<box> points = b.front().sample_points(m_num_samples);
    // If ∃p. ∀c. eval(c, p) = true, return 'SAT'
    unsigned count = 0;
    for (box const & p : points) {
        interruption_point();
        DREAL_LOG_DEBUG << "contractor_sample::prune -- sample " << ++count << "th point = " << p;
        bool check = true;
        for (shared_ptr<constraint> const ctr : m_ctrs) {
            if (ctr->get_type() == constraint_type::Nonlinear) {
                auto const nl_ctr = dynamic_pointer_cast<nonlinear_constraint>(ctr);
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(p);
                if (eval_result.first == l_False) {
                    check = false;
                    DREAL_LOG_DEBUG << "contractor_sample::prune -- sampled point = " << p << " does not satisfy " << *ctr;
                    break;
                }
            }
        }
        if (check) {
            DREAL_LOG_DEBUG << "contractor_sample::prune -- sampled point = " << p << " satisfies all constraints";
            b.front() = p;
            m_output = ibex::BitSet::all(b.front().size());
            return;
        }
    }
    m_output = ibex::BitSet::empty(b.front().size());
    return;
}


ostream & contractor_sample::display(ostream & out) const {
    out << "contractor_sample(" << m_num_samples << ")";
    return out;
}

contractor_aggressive::contractor_aggressive(unsigned const n, vector<shared_ptr<constraint>> const & ctrs)
    : contractor_cell(contractor_kind::SAMPLE), m_num_samples(n), m_ctrs(ctrs) {
}

void contractor_aggressive::prune(fbbox & b, SMTConfig &) const {
    DREAL_LOG_DEBUG << "contractor_eval::aggressive";
    m_input  = ibex::BitSet::empty(b.front().size());
    m_output = ibex::BitSet::empty(b.front().size());
    m_used_constraints.clear();
    // TODO(soonhok): set input & output
    // Sample n points
    set<box> points = b.front().sample_points(m_num_samples);
    // ∃c. ∀p. eval(c, p) = false   ===>  UNSAT
    for (shared_ptr<constraint> const ctr : m_ctrs) {
        interruption_point();
        if (ctr->get_type() == constraint_type::Nonlinear) {
            auto const nl_ctr = dynamic_pointer_cast<nonlinear_constraint>(ctr);
            bool check = false;
            for (box const & p : points) {
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(p);
                if (eval_result.first != l_False) {
                    check = true;
                    break;
                }
            }
            if (!check) {
                m_used_constraints.insert(ctr);
                pair<lbool, ibex::Interval> eval_result = nl_ctr->eval(b.front());
                DREAL_LOG_DEBUG << "Constraint: " << *nl_ctr << " is violated by all " << points.size() << " points";
                DREAL_LOG_DEBUG << "FYI, the interval evaluation gives us : " << eval_result.second;
                b.front().set_empty();
                return;
            }
        }
    }
}


ostream & contractor_aggressive::display(ostream & out) const {
    out << "contractor_aggressive(" << m_num_samples << ")";
    return out;
}

contractor mk_contractor_seq(initializer_list<contractor> const & l) {
    return contractor(make_shared<contractor_seq>(l));
}
contractor mk_contractor_seq(vector<contractor> const & v) {
    return contractor(make_shared<contractor_seq>(v));
}
contractor mk_contractor_seq(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_seq>(c1, c2));
}
contractor mk_contractor_try(contractor const & c) {
    return contractor(make_shared<contractor_try>(c));
}
contractor mk_contractor_try_or(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_try_or>(c1, c2));
}
contractor mk_contractor_throw() {
    return contractor(make_shared<contractor_throw>());
}
contractor mk_contractor_throw_if_empty(contractor const & c) {
    return contractor(make_shared<contractor_throw_if_empty>(c));
}
contractor mk_contractor_join(contractor const & c1, contractor const & c2) {
    return contractor(make_shared<contractor_join>(c1, c2));
}
contractor mk_contractor_ite(function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else) {
    return contractor(make_shared<contractor_ite>(guard, c_then, c_else));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, contractor const & c) {
    return contractor(make_shared<contractor_fixpoint>(guard, c));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, initializer_list<contractor> const & clist) {
    return contractor(make_shared<contractor_fixpoint>(guard, clist));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, vector<contractor> const & cvec) {
    return contractor(make_shared<contractor_fixpoint>(guard, cvec));
}
contractor mk_contractor_fixpoint(function<bool(box const &, box const &)> guard, initializer_list<vector<contractor>> const & cvec_list) {
    return contractor(make_shared<contractor_fixpoint>(guard, cvec_list));
}
contractor mk_contractor_int() {
    return contractor(make_shared<contractor_int>());
}
contractor mk_contractor_eval(shared_ptr<nonlinear_constraint> const ctr) {
    static unordered_map<shared_ptr<nonlinear_constraint>, contractor> eval_ctc_cache;
    auto const it = eval_ctc_cache.find(ctr);
    if (it == eval_ctc_cache.end()) {
        contractor ctc(make_shared<contractor_eval>(ctr));
        eval_ctc_cache.emplace(ctr, ctc);
        return ctc;
    } else {
        return it->second;
    }
}
contractor mk_contractor_cache(contractor const & ctc) {
    return contractor(make_shared<contractor_cache>(ctc));
}
contractor mk_contractor_sample(unsigned const n, vector<shared_ptr<constraint>> const & ctrs) {
    return contractor(make_shared<contractor_sample>(n, ctrs));
}
contractor mk_contractor_aggressive(unsigned const n, vector<shared_ptr<constraint>> const & ctrs) {
    return contractor(make_shared<contractor_aggressive>(n, ctrs));
}
ostream & operator<<(ostream & out, contractor const & c) {
    out << *(c.m_ptr);
    return out;
}

void contractor::prune_with_assert(box & b, SMTConfig & config) const {
    assert(m_ptr != nullptr);
    thread_local static box old_box(b);
    old_box = b;
    m_ptr->prune(b, config);
    if (!b.is_subset(old_box)) {
        cerr << "Pruning Violation: " << (*m_ptr) << endl;
        cerr << "Old Box" << endl
             << "==============" << endl
             << old_box << endl;
        cerr << "New Box" << endl
             << "==============" << endl
             << b << endl;
        cerr << "==============" << endl;
        display_diff(cerr, old_box, b);
        cerr << "==============" << endl;
        exit(1);
    }
}
}  // namespace dreal
