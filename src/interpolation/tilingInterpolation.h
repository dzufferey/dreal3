
#pragma once

#include <stack>
#include <tuple>
#include "util/box.h"
#include "constraint/constraint.h"
#include "opensmt/egraph/Enode.h"

namespace dreal {

class tilingInterpolation {

private:
    box domain;

    ibex::BitSet a_variables;
    ibex::BitSet b_variables;

    std::unordered_set<std::shared_ptr<constraint>> a_constraints;
    std::unordered_set<std::shared_ptr<constraint>> b_constraints;

    std::stack<std::tuple<bool,int,double,bool>> split_stack; //larger first, variable index, split value, first part done
    std::stack<Enode *> partial_interpolants;

    unsigned long int proof_size;

    bool equals(Enode * a, Enode * b);

    Enode * make_leq(int variable, double value);
    Enode * make_geq(int variable, double value);
    Enode * make_ite(int var, double upperBound, Enode * then, Enode * otherwise);
    Enode * make_and(Enode * a, Enode * b);
    Enode * make_or(Enode * a, Enode * b);
    Enode * make_true();
    Enode * make_false();

    bool is_a_var(int variable);
    bool is_b_var(int variable);
    bool is_shared_var(int variable);
    
    bool is_a_constraint(std::shared_ptr<constraint> c);
    bool is_b_constraint(std::shared_ptr<constraint> c);

    void push_partial_interpolant(Enode * i);

public:
    tilingInterpolation(box const & domain,
                        std::unordered_set<std::shared_ptr<constraint>> const & a_cstrs,
                        std::unordered_set<std::shared_ptr<constraint>> const & b_cstrs);

    void pruning(box const & old_box, box const & new_box, std::shared_ptr<constraint> cstr);

    void integer_pruning(box const & old_box, box const & new_box, int variable);

    void split(box const & first_box, box const & second_box, int variable);

    Enode * get_interpolant();

    void print_stats();
    unsigned long int get_proof_size();
    unsigned long int get_interpolant_size();
};

//a global reference to the interpolation
extern tilingInterpolation* interpolator;

}  // namespace dreal
