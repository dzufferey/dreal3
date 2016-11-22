#include "interpolation/tilingInterpolation.h"

#include <iostream>
#include "util/proof.h"
#include "opensmt/api/OpenSMTContext.h"
#include "util/logging.h"
#include "interpolation/interpolationUtils.h"

extern OpenSMTContext * parser_ctx;

namespace dreal {

using std::tuple;

tilingInterpolation::tilingInterpolation( box const & d,
        std::unordered_set<std::shared_ptr<constraint>> const & a_cstrs,
        std::unordered_set<std::shared_ptr<constraint>> const & b_cstrs):
    domain(d),
    a_variables(ibex::BitSet::empty(d.size())),
    b_variables(ibex::BitSet::empty(d.size())),
    a_constraints(a_cstrs),
    b_constraints(b_cstrs),
    split_stack(),
    partial_interpolants(),
    proof_size(0)
{
    for (auto c: a_cstrs) {
        for (Enode * v: c->get_vars()) {
            a_variables.add(d.get_index(v));
        }
    }
    for (auto c: b_cstrs) {
        for (Enode * v: c->get_vars()) {
            b_variables.add(d.get_index(v));
        }
    }
}

void tilingInterpolation::pruning(box const & old_box, box const & new_box, std::shared_ptr<constraint> cstr) {
    Enode * it;
    if (is_a_constraint(cstr)) {
        it = make_false();
    } else if (is_b_constraint(cstr)) {
        it = make_true();
    } else {
        assert(is_bound(cstr));
        DREAL_LOG_DEBUG << "pruning, ignoring bound: " << cstr.get();
        return;
    }
    if (new_box.is_empty()) {
        //if the new box is empty then we have a leaf
        push_partial_interpolant(it);
        proof_size += 1;
    } else {
        //we need to figure out what parts are pruned
        int max_var = domain.get_vars().size();
        for (int i = 0; i < max_var; i++) {
            auto const fst_value = old_box.get_value(i);
            auto const snd_value = new_box.get_value(i);
            //pruning on the lower end
            if (fst_value.lb() < snd_value.lb()) {
                std::tuple<bool,int,double,bool> pivot(false, i, snd_value.lb(), false);
                split_stack.push(pivot);
                push_partial_interpolant(it);
                proof_size += 1;
            }
            //pruning on the upper end
            if (fst_value.ub() > snd_value.ub()) {
                std::tuple<bool,int,double,bool> pivot(true, i, snd_value.ub(), false);
                split_stack.push(pivot);
                push_partial_interpolant(it);
                proof_size += 1;
            }
        }
    }
}

void tilingInterpolation::integer_pruning(box const & old_box, box const & new_box, int i) {
    Enode * it;
    //TODO what about shared ? should we rather take the projections
    if (is_a_var(i)) {
        it = make_false();
    } else {
        assert(is_b_var(i));
        it = make_true();
    }
    if (new_box.get_values()[i].is_empty()) {
        //if the new box is empty then we have a leaf
        push_partial_interpolant(it);
        proof_size += 1;
    } else {
        //we need to figure out what parts are pruned
        auto const fst_value = old_box.get_value(i);
        auto const snd_value = new_box.get_value(i);
        //pruning on the lower end
        if (fst_value.lb() < snd_value.lb()) {
            std::tuple<bool,int,double,bool> pivot(false, i, snd_value.lb(), false);
            split_stack.push(pivot);
            push_partial_interpolant(it);
            proof_size += 1;
        }
        //pruning on the upper end
        if (fst_value.ub() > snd_value.ub()) {
            std::tuple<bool,int,double,bool> pivot(true, i, snd_value.ub(), false);
            split_stack.push(pivot);
            push_partial_interpolant(it);
            proof_size += 1;
        }
    }
}

void tilingInterpolation::split(box const & first_box, box const & second_box, int variable) {
    std::tuple<double,bool> pivot = find_split(first_box, second_box, variable);
    split_stack.push(std::make_tuple(std::get<1>(pivot),variable,std::get<0>(pivot),false));
    proof_size += 1;
}

Enode * tilingInterpolation::get_interpolant() {
    //DREAL_LOG_DEBUG << "get_interpolant: splits " << split_stack.size() << ", partial " << partial_interpolants.size();
    assert(split_stack.size() == 0);
    assert(partial_interpolants.size() == 1);
    return partial_interpolants.top();
}

unsigned long count_enodes(const Enode * n ) {
    if (n == NULL) {
        return  0;
    } else {
        auto ca = count_enodes(n->getCar());
        auto cd = count_enodes(n->getCdr());
        if (n->isTerm() /*&& n->hasSortBool()*/) {
            return ca + cd + 1;
        } else {
            return ca + cd;
        }
    }
}

unsigned long count_ineq(const Enode * n ) {
    if (n == NULL) {
        return  0;
    } else {
        auto ca = count_ineq(n->getCar());
        auto cd = count_ineq(n->getCdr());
        if (n->isTerm() && (n->isLeq() || n->isGeq())) {
            return ca + cd + 1;
        } else {
            return ca + cd;
        }
    }
}

void tilingInterpolation::print_stats() {
    Enode * itp = get_interpolant();
    std::cout << "proof size: " << proof_size << std::endl;
    std::cout << "interpolant size: " << count_enodes(itp) << std::endl;
    std::cout << "#inequalities: " << count_ineq(itp) << std::endl;
}

unsigned long int tilingInterpolation::get_proof_size() {
    return proof_size;
}

unsigned long int tilingInterpolation::get_interpolant_size() {
    Enode * itp = get_interpolant();
    return count_ineq(itp);
}

void tilingInterpolation::push_partial_interpolant(Enode * i) {
    DREAL_LOG_DEBUG << "push_partial_interpolant: splits " << split_stack.size() << ", partial " << partial_interpolants.size();
    if (split_stack.empty()) {
        assert(partial_interpolants.empty());
        partial_interpolants.push(i);
    } else {
        std::tuple<bool,int,double,bool> top = split_stack.top();
        split_stack.pop();
        if (std::get<3>(top) == true) {
            Enode * it2 = partial_interpolants.top();
            partial_interpolants.pop();
            int variable = std::get<1>(top);
            if (is_shared_var(variable)) {
                if (std::get<0>(top)) {
                    i = make_ite(variable, std::get<2>(top), i, it2);
                } else {
                    i = make_ite(variable, std::get<2>(top), it2, i);
                }
            } else if (is_a_var(variable)) {
                i = make_or(i, it2);
            } else {
                assert(is_b_var(variable));
                i = make_and(i, it2);
            }
            push_partial_interpolant(i);
        } else {
            partial_interpolants.push(i);
            std::get<3>(top) = true;
            split_stack.push(top);
        }
    }
}

bool tilingInterpolation::is_a_var(int variable) {
    return a_variables[variable];
}

bool tilingInterpolation::is_b_var(int variable) {
    return b_variables[variable];
}

bool tilingInterpolation::is_shared_var(int variable) {
    return is_a_var(variable) && is_b_var(variable);
}
    
bool tilingInterpolation::is_a_constraint(std::shared_ptr<constraint> c) {
    return a_constraints.count(c) > 0;
}

bool tilingInterpolation::is_b_constraint(std::shared_ptr<constraint> c) {
    return b_constraints.count(c) > 0;
}
    
Enode * tilingInterpolation::make_leq(int variable, double value) {
    Enode * v = domain.get_vars()[variable];
    Enode * c = parser_ctx->mkNum(value);
    Enode * args = parser_ctx->mkCons(v, parser_ctx->mkCons(c));
    return parser_ctx->mkLeq( args );
}

Enode * tilingInterpolation::make_geq(int variable, double value) {
    Enode * v = domain.get_vars()[variable];
    Enode * c = parser_ctx->mkNum(value);
    Enode * args = parser_ctx->mkCons(v, parser_ctx->mkCons(c));
    return parser_ctx->mkGeq( args );
}

//TODO this part leaks memory
Enode * tilingInterpolation::make_ite(int variable, double upperBound, Enode * then, Enode * otherwise) {
    if (equals(then, otherwise)) {
        return then;
    } else {
        auto left =  make_and(make_leq(variable, upperBound), then);
        auto right = make_and(make_geq(variable, upperBound), otherwise);
        return make_or(left, right);
    }
}

//TODO this part leaks memory
Enode * tilingInterpolation::make_and(Enode * a, Enode * b) {
    if (a->isTrue() || b->isFalse()) {
        return b;
    } else if (b->isTrue() || a->isFalse()) {
        return a;
    } else if (equals(a, b)) {
        return a;
    } else if (( (a->isGeq() && b->isLeq()) ||
                 (a->isLeq() && b->isGeq()) ) &&
               equals(a->get1st(), b->get1st()) &&
               equals(a->get2nd(), b->get2nd()) ) {
        return parser_ctx->mkTrue();
    } else {
        Enode * args = parser_ctx->mkCons(a, parser_ctx->mkCons(b));
        return parser_ctx->mkAnd( args );
    }
}

//TODO this part leaks memory
Enode * tilingInterpolation::make_or(Enode * a, Enode * b) {
    if (a->isTrue() || b->isFalse()) {
        return a;
    } else if (b->isTrue() || a->isFalse()) {
        return b;
    } else if (equals(a, b)) {
        return a;
    } else {
        Enode * args = parser_ctx->mkCons(a, parser_ctx->mkCons(b));
        return parser_ctx->mkOr( args );
    }
}

Enode * tilingInterpolation::make_true() {
    return parser_ctx->mkTrue();
}

Enode * tilingInterpolation::make_false() {
    return parser_ctx->mkFalse();
}

bool tilingInterpolation::equals(Enode * a, Enode * b) {
    if (a == NULL && b == NULL) {
      return true;
    } else if (a == NULL || b == NULL) {
      return false;
    }
    return (a->isTerm() && b->isTerm() &&
            a->hasValue() && b->hasValue() &&
            a->getValue() == b->getValue()) ||
           (a->getId() == b->getId() &&
            a->getArity() == b->getArity() &&
            equals(a->getCar(), b->getCar()) &&
            equals(a->getCdr(), b->getCdr()));
}

tilingInterpolation* interpolator = NULL;

}
