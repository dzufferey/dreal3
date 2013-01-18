#include "nra_solver.h"
#include "icp_solver.h"
#include <boost/algorithm/string/predicate.hpp>

NRASolver::NRASolver( const int           i
                      , const char *        n
                      , SMTConfig &         c
                      , Egraph &            e
                      , SStore &            t
                      , vector< Enode * > & x
                      , vector< Enode * > & d
                      , vector< Enode * > & s
    )
    : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{
//initialize icp solver first

}

NRASolver::~NRASolver( )
{
    // Here Deallocate External Solver
}

void debug_print_env(const map<Enode*, pair<double, double> > & env)
{
    for(map<Enode*, pair<double, double> >::const_iterator ite = env.begin();
        ite != env.end();
        ite++)
    {
        Enode* key = (*ite).first;
        double lb =  (*ite).second.first;
        double ub =  (*ite).second.second;
        cout << "Key: " << key << "\t Value: [" << lb << ", " << ub << "]" << endl;
    }
}

void debug_print_stack(const vector<Enode*> & stack)
{
    // Print out all the Enode in stack
    for(vector<Enode*>::const_iterator ite = stack.begin();
        ite != stack.end();
        ite++)
    {
        cerr << *ite << endl;
    }
}

void debug_print_explanation (const vector<Enode*> & explanation)
{
    for (vector<Enode *>::const_iterator it = explanation.begin(); it!= explanation.end(); it++)
    {
        cout << *it <<" with polarity "
             << toInt((*it)->getPolarity()) << " ";
    }
    cout<< endl;
}

set<Enode *> NRASolver::get_variables (Enode * e )
{
    set<Enode *> result;
    Enode * p = NULL;
    if( e->isSymb( ) ) { /* do nothing */ }
    else if ( e->isNumb( ) ) { /* do nothing */ }
    else if ( e->isTerm( ) )
    {
        if ( e -> isVar() ) { result.insert(e); }
        set<Enode*> tmp_set = get_variables(e->getCar());
        result.insert(tmp_set.begin(), tmp_set.end());
        p = e->getCdr();
        while ( !p->isEnil( ) )
        {
            tmp_set = get_variables(p->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());
            p = p->getCdr();
        }
    }
    else if ( e->isList( ) )
    {
        if ( !e->isEnil( ) )
        {
            set <Enode*> tmp_set = get_variables(e->getCar());
            result.insert(tmp_set.begin(), tmp_set.end());

            p = e->getCdr();
            while ( !p->isEnil( ) )
            {
                tmp_set = get_variables(p->getCar());
                result.insert(tmp_set.begin(), tmp_set.end());
                p = p->getCdr();
            }
        }
    }
    else if ( e->isDef( ) ) { /* do nothing */ }
    else if ( e->isEnil( ) ) { /* do nothing */ }
    else  opensmt_error( "unknown case value" );
    return result;
}

// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is
// called before the actual solving starts.
//
lbool NRASolver::inform( Enode * e )
{
    cerr << "================================================================" << endl;
    cerr << "NRASolver::inform: " << e << endl;
    cerr << "================================================================" << endl;
    assert( e -> isAtom() );

    set<Enode*> variables_in_e = get_variables(e);

    for(set<Enode*>::iterator ite = variables_in_e.begin();
        ite != variables_in_e.end();
        ite++)
    {
        cerr << *ite << endl;
        double lb = (*ite)->getLowerBound();
        double ub = (*ite)->getUpperBound();
        env[*ite] = make_pair (lb, ub);
    }
    return l_Undef;
}

//
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool NRASolver::assertLit ( Enode * e, bool reason )
{
    cerr << "================================================================" << endl;
    cerr << "NRASolver::assertLit: " << e << ", " << reason << endl;
    cerr << "================================================================" << endl;

    (void)reason;
    assert( e );
    assert( belongsToT( e ) );

    assert( e->hasPolarity( ) );
    assert( e->getPolarity( ) == l_False
            || e->getPolarity( ) == l_True );

    if ( e->isDeduced( )
         && e->getPolarity( ) == e->getDeduced( )
         && e->getDedIndex( ) == id ) {
        cerr << "NRASolver::assertLit: DEDUCED" << e << endl;
        return true;
    }
    stack.push_back(e);
    return true;
}

//
// Saves a backtrack point
// You are supposed to keep track of the
// operations, for instance in a vector
// called "undo_stack_term", as happens
// in EgraphSolver
//
void NRASolver::pushBacktrackPoint ( )
{
    cerr << "================================================================" << endl;
    cerr << "NRASolver::pushBacktrackPoint " << stack.size() << endl;

    undo_stack_size.push_back(stack.size());
    env_stack.push_back(env);
}

//
// Restore a previous state. You can now retrieve
// the size of the stack when you pushed the last
// backtrack point. You have to implement the
// necessary backtrack operations
// (see for instance backtrackToStackSize( )
// in EgraphSolver)
// Also make sure you clean the deductions you
// did not communicate
//
void NRASolver::popBacktrackPoint ( )
{
    cerr << "================================================================" << endl;
    cerr << "NRASolver::popBacktrackPoint" << endl;

    vector<Enode*>::size_type prev_size = undo_stack_size.back( );
    undo_stack_size.pop_back();
    while (stack.size() > prev_size) {
        cerr << "Popped Literal = " << stack.back() << endl;
        stack.pop_back();
    }

    cerr << "======= Before Pop, Env =                                       " << endl;
    debug_print_env(env);

    env_stack.pop_back();
    env = env_stack.back();

    cerr << "======= After Pop, Env =                                        " << endl;
    debug_print_env(env);
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool NRASolver::check( bool complete )
{
    cerr << "================================================================" << endl;
    cerr << "NRASolver::check " << (complete ? "complete" : "incomplete") << endl;
    bool result = true;
    debug_print_stack(stack);
    debug_print_env(env);

    if(!complete) {
        // Incomplete Check
        result = true;
    } else {
        // Complete Check
        explanation.clear();
        icp_solver solver( stack, env, explanation, 10.0 );
        result = solver.solve();
        if (!result) {
            cout<<"#explanation provided: ";
            debug_print_explanation(explanation);
        }
    }
    return result;
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool NRASolver::belongsToT( Enode * e )
{
    (void)e;
    assert( e );
    return true;
}

//
// Copy the model into enode's data
//
void NRASolver::computeModel( )
{
    cerr << "computeModel" << endl;
}

#ifdef PRODUCE_PROOF
Enode * NRASolver::getInterpolants( )
{
    return NULL;
}
#endif
