
#pragma once

#include <tuple>
#include <unordered_set>
#include "constraint/constraint.h"
#include "opensmt/egraph/Enode.h"

namespace dreal {

tuple<unordered_set<constraint const *>, unordered_set<constraint const *>> splitAB(const std::vector<constraint const *> & cstrs);

}

