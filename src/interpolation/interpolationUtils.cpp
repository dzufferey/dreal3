#include "interpolation/interpolationUtils.h"

#include <sstream>

namespace dreal {

tuple<unordered_set<constraint const *>, unordered_set<constraint const *>> splitAB(const scoped_vec<constraint const *> cstrs) {
    unordered_set<constraint const *> a_cstrs;
    unordered_set<constraint const *> b_cstrs;
    std::stringstream sstr;
    for (auto c: cstrs) {
        bool is_a = false;
        bool is_b = false;
        for (auto n: c->get_enodes()){
            auto a = n->get_attribute(); 
            if (a != NULL) {
                if (*a == "A") {
                    is_a = true;
                } else if (*a == "B") {
                    is_b = true;
                }
                sstr.clear();
            }
        }
        assert(!(is_a && is_b));// constraint in both A and B. we might lift this later.
        assert(is_a || is_b); // constraint neither in A nor B.
        if (is_a) {
            a_cstrs.insert(c);
        }
        if (is_b) {
            b_cstrs.insert(c);
        }
    }
    return tuple<unordered_set<constraint const *>, unordered_set<constraint const *>>(a_cstrs, b_cstrs);
}

}
