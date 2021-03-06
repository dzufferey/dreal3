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
#include <atomic>
#include <cassert>
#include <condition_variable>
#include <initializer_list>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include "./config.h"
#include "contractor/contractor_common.h"
#include "opensmt/egraph/Enode.h"
#include "opensmt/smtsolvers/SMTConfig.h"
#include "util/box.h"
#include "constraint/constraint.h"

namespace dreal {

// contractor_parallel : Run C1, C2, ... , Cn in parallel.
class contractor_parallel : public contractor_cell {
private:
    std::vector<contractor> m_vec;
    mutable std::mutex m_mutex;
    mutable std::condition_variable m_cv;
    mutable int m_index;

public:
    explicit contractor_parallel(std::initializer_list<contractor> const & l);
    explicit contractor_parallel(std::vector<contractor> const & v);
    contractor_parallel(contractor const & c1, contractor const & c2);
    void prune(fbbox & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

class contractor_pseq : public contractor_cell {
private:
    contractor m_ctc;
    std::vector<contractor> m_vec;
    bool m_use_threads;
    void init();

public:
    explicit contractor_pseq(std::initializer_list<contractor> const & l);
    explicit contractor_pseq(std::vector<contractor> const & v);
    void prune(fbbox & b, SMTConfig & config) const;
    std::ostream & display(std::ostream & out) const;
};

contractor mk_contractor_parallel(std::initializer_list<contractor> const & l);
contractor mk_contractor_parallel(std::vector<contractor> const & v);
contractor mk_contractor_parallel(contractor const & c1, contractor const & c2);

contractor mk_contractor_pseq(std::initializer_list<contractor> const & l);
contractor mk_contractor_pseq(std::vector<contractor> const & v);

}  // namespace dreal
