#include "interpolation/interpolationUtils.h"
#include "util/logging.h"

namespace dreal {

std::tuple<std::unordered_set<std::shared_ptr<constraint>>,
           std::unordered_set<std::shared_ptr<constraint>>>
        splitAB(const std::vector<std::shared_ptr<constraint>> & cstrs) {
    std::unordered_set<std::shared_ptr<constraint>> a_cstrs(100);
    std::unordered_set<std::shared_ptr<constraint>> b_cstrs(100);
    for (auto c: cstrs) {
        bool is_a = false;
        bool is_b = false;
        assert(c.get() != NULL);
        DREAL_LOG_DEBUG << "splitAB, c.get: " << c.get() ;
        DREAL_LOG_DEBUG << "splitAB, c.get_enodes: " << c->get_enodes().size() ;
        for (Enode const * n: c->get_enodes()){
            assert(n != NULL);
            auto a = n->get_attribute(); 
            if (a != NULL) {
                if (*a == "A") {
                    is_a = true;
                    DREAL_LOG_DEBUG << n << " has side A";
                } else if (*a == "B") {
                    is_b = true;
                    DREAL_LOG_DEBUG << n << " has side B";
                } else {
                    DREAL_LOG_DEBUG << n << " has no side ??? " << *a;
                }
            } else {
                DREAL_LOG_DEBUG << n << " has no attribute";
            }
        }
        assert(is_a || is_b); // constraint neither in A nor B.
        if (is_a) {
            a_cstrs.insert(c);
        } else if (is_b) {
            b_cstrs.insert(c);
        }
    }
    return std::tuple<std::unordered_set<std::shared_ptr<constraint>>, std::unordered_set<std::shared_ptr<constraint>>>(a_cstrs, b_cstrs);
}

bool is_bound(std::shared_ptr<constraint> & cstr) {
  for (Enode const * n: cstr->get_enodes()){
    if ((n->isGeq() || n->isLeq()) &&
        ( (n->get1st()->isVar() && n->get2nd()->hasValue()) ||
          (n->get2nd()->isVar() && n->get1st()->hasValue()) )
       ) {
      //it is a bound, nothing to do
    } else {
      return false;
    }
  }
  return true;
}

}
