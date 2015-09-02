
#include "util/fbbox.h"

namespace dreal {

fbbox::fbbox(box const & model): b1(model), b2(model), swapped(false) {}
    
fbbox::fbbox(const fbbox & source): b1(source.b1), b2(source.b2), swapped(source.swapped) {
    std::cerr << "warning, copy constructor used on fbbox, this class is meant to be used with references" << std::endl;
}

}
