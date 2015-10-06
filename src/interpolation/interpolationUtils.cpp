#include "interpolation/interpolationUtils.h"

namespace dreal {

tuple<unordered_set<constraint const *>, unordered_set<constraint const *>> splitAB(const std::vector<constraint const *> & cstrs) {
    unordered_set<constraint const *> a_cstrs(100);
    unordered_set<constraint const *> b_cstrs(100);
    for (constraint const * c: cstrs) {
        bool is_a = false;
        bool is_b = false;
        assert(c != NULL);
        for (Enode const * n: c->get_enodes()){
            assert(n != NULL);
            auto a = n->get_attribute(); 
            if (a != NULL) {
                if (*a == "A") {
                    is_a = true;
                } else if (*a == "B") {
                    is_b = true;
                }
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
