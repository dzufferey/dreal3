
#pragma once

#include <tuple>
#include <unordered_set>
#include "constraint/constraint.h"
#include "opensmt/egraph/Enode.h"

namespace dreal {

std::tuple<std::unordered_set<std::shared_ptr<constraint>>, std::unordered_set<std::shared_ptr<constraint>>>
    splitAB(const std::vector<std::shared_ptr<constraint>> & cstrs);

bool is_bound(std::shared_ptr<constraint> & cstr);

}

