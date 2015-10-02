
#pragma once

#include <tuple>
#include <unordered_set>
#include "constraint/constraint.h"
#include "opensmt/egraph/Enode.h"
#include "util/scoped_vec.h"

namespace dreal {

tuple<unordered_set<constraint const *>, unordered_set<constraint const *>> splitAB(const scoped_vec<constraint const *>  cstrs);

}

