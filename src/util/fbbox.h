
#pragma once
#include "util/box.h"


namespace dreal {

/** A "front/back" box: analogy with double buffering in CG
 *  The font box contains the current state and the back box is used as buffer for computations.
 *  When the computation is done, the front and back boxes can be swapped.
 *  The value of the back can be arbitrary, it should not be assumed that they correspond to a previous step.
 */
class fbbox {

private:
    box b1;
    box b2;
    bool swapped;

public:
    fbbox(box const & model);

    explicit fbbox(const fbbox & source);

    inline box & front() {
        if (swapped) return b2;
        else return b1;
    }
    
    inline box & back() {
        if (swapped) return b1;
        else return b2;
    }

    inline void swap() {
        swapped = !swapped;
    }

};

}
