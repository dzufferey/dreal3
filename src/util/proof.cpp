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

#include <ostream>
#include <string>
#include "util/hexfloat.h"
#include "util/proof.h"
#include "util/box.h"


namespace dreal {

using std::endl;
using std::string;

void output_start(ostream & out, box const & domain, bool const readable_proof) {
    out << "[domain]" << endl;
    dreal::display(out, domain, !readable_proof);
    out.put(out.widen('\n')); //avoid flushing
}

void output_pruning_step(ostream & out, box const & old_box, box const & new_box, bool const readable_proof, string const & constraint) {
    if (old_box != new_box) {
        bool empty = new_box.is_empty();
        if (empty) {
            out << "[conflict detected]";
        } else {
            out << "[after pruning]";
        }
        if (constraint.length() > 0) {
            out << " by " << constraint;
        }
        if (!empty) {
            out.put(out.widen('\n')); //avoid flushing
            dreal::display(out, new_box, !readable_proof);
        }
        out.put(out.widen('\n')); //avoid flushing
        //out << endl; //flush here
    }
}

//determine where the split happens and the direction
std::tuple<double,bool> find_split(box const & first_box, box const & second_box, int variable) {
    auto const fst_value = first_box.get_value(variable);
    auto const snd_value = second_box.get_value(variable);
    double split;
    bool gt;
    if (fst_value.ub() <= snd_value.lb() ) {
        assert( fst_value.lb() < snd_value.ub() );
        split = fst_value.ub();
        gt = false;
    } else {
        assert( snd_value.lb() < fst_value.ub() );
        split = fst_value.lb();
        gt = true;
    }
    return std::make_pair(split, gt);
}

void output_split_step(std::ostream & out, box const & old_box,
                       box const & first_box, box const & second_box,
                       bool const readable_proof, int variable) {
  auto const p = find_split(first_box, second_box, variable);
  double split = get<0>(p);
  bool gt = get<1>(p);
  //printing
  out << "[branching] on (";
  if (gt) {
    out << ">= ";
  } else {
    out << "<= ";
  }
  out << old_box.get_name(variable) << " ";
  if (readable_proof) {
    out << split;
  } else {
    out << to_hexfloat(split);
  }
  out << ")";
  out.put(out.widen('\n')); //avoid flushing
  //out << endl;
}

}  // namespace dreal
