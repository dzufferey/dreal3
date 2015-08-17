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
#include <string>
#include "util/box.h"

namespace dreal {
void output_start(std::ostream & out, box const & domain, bool const readable_proof);
void output_pruning_step(std::ostream & out, box const & old_box, box const & new_box, bool const readable_proof, std::string const & constraint);
void output_split_step(std::ostream & out, box const & old_box, box const & first_box, box const & second_box, bool const readable_proof, int variable);
}  // namespace dreal
