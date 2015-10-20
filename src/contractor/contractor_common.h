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

#pragma once
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <string>
#include <memory>
#include <utility>
#include "./config.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "util/fbbox.h"
#include "constraint/constraint.h"

namespace dreal {
enum class contractor_kind { SEQ, OR, ITE, FP, PARALLEL,
        TIMEOUT, TRY, TRY_OR, JOIN,
        IBEX_FWDBWD, IBEX_NEWTON, IBEX_HC4, IBEX_POLYTOPE,
        INT, EVAL, CACHE, SAMPLE, AGGRESSIVE, FORALL,
        THROW, THROW_IF_EMPTY,
#ifdef SUPPORT_ODE
        CAPD_FULL, CAPD_SIMPLE, GSL,
#endif
        };

class contractor_exception : public std::runtime_error {
public:
    explicit contractor_exception(const std::string& what_arg) : runtime_error(what_arg) { }
    explicit contractor_exception(const char* what_arg) : runtime_error(what_arg) { }
};

// Base Cell
class contractor_cell {
protected:
    contractor_kind m_kind;
    //TODO DZ: maybe we could push those to the fbbox and makes the contractor more thread-safe
    mutable ibex::BitSet m_input;
    mutable ibex::BitSet m_output;
    mutable std::unordered_set<std::shared_ptr<constraint>> m_used_constraints;
public:
    explicit contractor_cell(contractor_kind kind) : m_kind(kind) { }
    contractor_cell(contractor_kind kind, unsigned n)
        : m_kind(kind), m_input(ibex::BitSet::empty(n)), m_output(ibex::BitSet::all(n)) { }
    virtual ~contractor_cell() noexcept { }
    inline ibex::BitSet input()  const { return m_input; }
    inline ibex::BitSet output() const { return m_output; }
    inline std::unordered_set<std::shared_ptr<constraint>> used_constraints() const { return m_used_constraints; }
    inline void prune(box & b, SMTConfig & config) const {
      fbbox fbb(b);
      prune(fbb, config);
      b = fbb.front();
    };
    virtual void prune(fbbox & b, SMTConfig & config) const = 0;
    virtual std::ostream & display(std::ostream & out) const = 0;
};

std::ostream & operator<<(std::ostream & out, contractor_cell const & c);

// Wrapper on contractor_cell and its derived classes
class contractor {
private:
    std::shared_ptr<contractor_cell const> m_ptr;

public:
    contractor() : m_ptr(nullptr) { }
    explicit contractor(std::shared_ptr<contractor_cell> const c) : m_ptr(c) {
        assert(m_ptr != nullptr);
    }
    contractor(contractor const & c) : m_ptr(c.m_ptr) {
        assert(m_ptr);
    }
    contractor(contractor && c) noexcept : m_ptr(std::move(c.m_ptr)) {}
    ~contractor() noexcept { }

    friend void swap(contractor & c1, contractor & c2) {
        using std::swap;
        swap(c1.m_ptr, c2.m_ptr);
    }

    contractor& operator=(contractor c) {
        swap(*this, c);
        return *this;
    }

    inline ibex::BitSet input() const { return m_ptr->input(); }
    inline ibex::BitSet output() const { return m_ptr->output(); }
    inline std::unordered_set<std::shared_ptr<constraint>> used_constraints() const { return m_ptr->used_constraints(); }
    inline void prune(box & b, SMTConfig & config) const {
        if (m_ptr) {
            m_ptr->prune(b, config);
        }
    }
    inline void prune(fbbox & b, SMTConfig & config) const {
        if (m_ptr) {
            m_ptr->prune(b, config);
        }
    }
    void prune_with_assert(box & b, SMTConfig & config) const;
    inline bool operator==(contractor const & c) const { return m_ptr == c.m_ptr; }
    inline bool operator<(contractor const & c) const { return m_ptr < c.m_ptr; }

    friend contractor mk_contractor_ibex_fwdbwd(std::shared_ptr<nonlinear_constraint> const ctr);
    friend contractor mk_contractor_ibex_newton(box const & box, std::shared_ptr<nonlinear_constraint> const ctr);
    friend contractor mk_contractor_ibex_hc4(std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
    friend contractor mk_contractor_ibex_polytope(double const prec, std::vector<std::shared_ptr<nonlinear_constraint>> const & ctrs);
    friend contractor mk_contractor_seq(std::initializer_list<contractor> const & l);
    friend contractor mk_contractor_seq(std::vector<contractor> const & v);
    friend contractor mk_contractor_seq(contractor const & c1, contractor const & c2);
    friend contractor mk_contractor_parallel(std::initializer_list<contractor> const & l);
    friend contractor mk_contractor_parallel(std::vector<contractor> const & v);
    friend contractor mk_contractor_parallel(contractor const & c1, contractor const & c2);
    friend contractor mk_contractor_try(contractor const & c);
    friend contractor mk_contractor_try_or(contractor const & c1, contractor const & c2);
    friend contractor mk_contractor_throw();
    friend contractor mk_contractor_throw_if_empty(contractor const & c);
    friend contractor mk_contractor_join(contractor const & c1, contractor const & c2);
    friend contractor mk_contractor_ite(std::function<bool(box const &)> guard, contractor const & c_then, contractor const & c_else);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, contractor const & c);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::initializer_list<contractor> const & clist);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::vector<contractor> const & cvec);
    friend contractor mk_contractor_fixpoint(std::function<bool(box const &, box const &)> guard, std::initializer_list<std::vector<contractor>> const & cvec_list);
    friend contractor mk_contractor_int();
    friend contractor mk_contractor_eval(std::shared_ptr<nonlinear_constraint> const ctr);
    friend contractor mk_contractor_cache(contractor const & ctc);
    friend contractor mk_contractor_sample(unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
    friend contractor mk_contractor_aggressive(unsigned const n, std::vector<std::shared_ptr<constraint>> const & ctrs);
#ifdef SUPPORT_ODE
    friend contractor mk_contractor_capd_simple(box const & box, std::shared_ptr<ode_constraint> const ctr, bool const forward);
    friend contractor mk_contractor_capd_full(box const & box, std::shared_ptr<ode_constraint> const ctr, bool const forward, unsigned const taylor_order, unsigned const grid_size, double const timeout);
    friend contractor mk_contractor_gsl(box const & box, std::shared_ptr<ode_constraint> const ctr, contractor const & eval_ctc, bool const forward, double const timeout);
#endif
    std::size_t hash() const { return (std::size_t) m_ptr.get(); }
    friend std::ostream & operator<<(std::ostream & out, contractor const & c);
};

}  // namespace dreal

namespace std {
template <>
struct hash<dreal::contractor> {
    std::size_t operator()(dreal::contractor const & c) const { return c.hash(); }
};
}  // namespace std
