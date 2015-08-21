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

#pragma once
#include <iostream>
#include <chrono>
#include <atomic>
#include <cstdint>
namespace dreal {
class stat {
    std::atomic<std::uint_fast64_t> m_num_of_incomplete_check;
    std::atomic<std::uint_fast64_t> m_num_of_complete_check;
    std::atomic<std::uint_fast64_t> m_num_of_assert;
    std::atomic<std::uint_fast64_t> m_num_of_push;
    std::atomic<std::uint_fast64_t> m_num_of_pop;
    std::atomic<std::uint_fast64_t> m_num_of_branch;
    std::atomic<std::uint_fast64_t> m_num_of_prune;
public:
    std::chrono::time_point<std::chrono::high_resolution_clock> m_start_time;
    stat();
    void reset();
    void increase_check(bool complete);
    void increase_assert();
    void increase_push();
    void increase_pop();
    void increase_branch();
    void increase_prune();
    friend std::ostream & operator<<(std::ostream & out, stat const & stat);
};

std::ostream & operator<<(std::ostream & out, stat const & stat);
}  // namespace dreal
