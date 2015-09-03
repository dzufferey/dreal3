/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include <vector>
#include <tuple>
#include <random>
#include <thread>

#include "icp/icp.h"
#include "util/logging.h"
#include "util/stat.h"
#include "util/proof.h"
#include "util/fbbox.h"

namespace dreal {

void output_solution(box const & b, SMTConfig & config, unsigned i) {
    if (i > 0) {
        cout << i << "-th ";
    }
    cout << "Solution:" << endl;
    cout << b << endl;
    if (!config.nra_model_out.is_open()) {
        config.nra_model_out.open(config.nra_model_out_name.c_str(), std::ofstream::out | std::ofstream::trunc);
        if (config.nra_model_out.fail()) {
            cout << "Cannot create a file: " << config.nra_model_out_name << endl;
            exit(1);
        }
    }
    display(config.nra_model_out, b, false, true);
}

box naive_icp::solve(box b, contractor const & ctc, SMTConfig & config) {
    vector<box> solns;
    vector<box> box_stack;
    box_stack.push_back(b);
    DREAL_LOG_INFO << "icp_loop call with: " << b;
    fbbox fbb(b);
    do {
        DREAL_LOG_INFO << "icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        fbb.front() = box_stack.back();
        box_stack.pop_back();
        try {
            DREAL_LOG_INFO << "before pruning, front: " << fbb.front();
            DREAL_LOG_INFO << "before pruning,  back: " << fbb.back() << std::endl;
            ctc.prune(fbb, config);
            DREAL_LOG_INFO << "after pruning, front: " << fbb.front();
            DREAL_LOG_INFO << "after pruning,  back: " << fbb.back() << std::endl;
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!fbb.front().is_empty()) {
            //TODO we should be able to save some copying by splitting directly the fbb using back and front
            //we could also skip some copying if we do not push the next branch on the stack
            tuple<int, box, box> splits = fbb.front().bisect(config.nra_precision);
            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, fbb.front(), first, second,
                                          config.nra_readable_proof, i);
                    }
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, fbb.front(), second, first,
                                          config.nra_readable_proof, i);
                    }
                }
            } else {
                config.nra_found_soln++;
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
                if (config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(fbb.front(), config, config.nra_found_soln);
                }
                solns.push_back(fbb.front());
            }
        }
    } while (box_stack.size() > 0);
    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        b = fbb.front();
        assert(!b.is_empty() || box_stack.size() == 0);
        // cerr << "BEFORE ADJUST_BOUND\n==================\n" << b << "=========================\n\n\n";
        b.adjust_bound(box_stack);
        // cerr << "AFTER  ADJUST_BOUND\n==================\n" << b << "=========================\n\n\n";
        return b;
    }
}

/*
box naive_icp::solve(box b, contractor const & ctc, SMTConfig & config) {
    vector<box> solns;
    vector<box> box_stack;
    box_stack.push_back(b);
    do {
        DREAL_LOG_INFO << "icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        box_stack.pop_back();
        try {
            b = ctc.prune(b, config);
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!b.is_empty()) {
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, b, first, second,
                                          config.nra_readable_proof, i);
                    }
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, b, second, first,
                                          config.nra_readable_proof, i);
                    }
                }
            } else {
                config.nra_found_soln++;
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
                if (config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(b, config, config.nra_found_soln);
                }
                solns.push_back(b);
            }
        }
    } while (box_stack.size() > 0);
    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        assert(!b.is_empty() || box_stack.size() == 0);
        // cerr << "BEFORE ADJUST_BOUND\n==================\n" << b << "=========================\n\n\n";
        b.adjust_bound(box_stack);
        // cerr << "AFTER  ADJUST_BOUND\n==================\n" << b << "=========================\n\n\n";
        return b;
    }
}
*/

box ncbt_icp::solve(box b, contractor const & ctc, SMTConfig & config) {
    static unsigned prune_count = 0;
    vector<box> box_stack;
    vector<int> bisect_var_stack;
    box_stack.push_back(b);
    bisect_var_stack.push_back(-1);  // Dummy var
    do {
        // Loop Invariant
        assert(box_stack.size() == bisect_var_stack.size());
        DREAL_LOG_INFO << "new_icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        try {
            b = ctc.prune(b, config);
            if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
        } catch (contractor_exception & e) {
            // Do nothing
        }
        prune_count++;
        box_stack.pop_back();
        bisect_var_stack.pop_back();
        if (!b.is_empty()) {
            // SAT
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
            int const index = get<0>(splits);
            if (index >= 0) {
                box const & first    = get<1>(splits);
                box const & second   = get<2>(splits);
                if (second.is_bisectable()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, b, first, second,
                                          config.nra_readable_proof, index);
                    }
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, b, second, first,
                                          config.nra_readable_proof, index);
                    }
                }
                bisect_var_stack.push_back(index);
                bisect_var_stack.push_back(index);
            } else {
                break;
            }
        } else {
            // UNSAT
            while (box_stack.size() > 0) {
                assert(box_stack.size() == bisect_var_stack.size());
                int bisect_var = bisect_var_stack.back();
                ibex::BitSet const & input = ctc.input();
                DREAL_LOG_DEBUG << ctc;
                if (!input[bisect_var]) {
                    box_stack.pop_back();
                    bisect_var_stack.pop_back();
                } else {
                    break;
                }
            }
        }
    } while (box_stack.size() > 0);
    DREAL_LOG_DEBUG << "prune count = " << prune_count;
    b.adjust_bound(box_stack);
    return b;
}

bool random_icp::random_bool() {
    static thread_local std::mt19937_64 rg(std::chrono::system_clock::now().time_since_epoch().count());
    std::uniform_real_distribution<double> m_dist(0, 1);
    return m_dist(rg) >= 0.5;
}

box random_icp::solve(box b, contractor const & ctc, SMTConfig & config ) {
    vector<box> solns;
    vector<box> box_stack;
    box_stack.push_back(b);
    do {
        DREAL_LOG_INFO << "icp_loop()"
                       << "\t" << "box stack Size = " << box_stack.size();
        b = box_stack.back();
        box_stack.pop_back();
        try {
            b = ctc.prune(b, config);
        } catch (contractor_exception & e) {
            // Do nothing
        }
        if (!b.is_empty()) {
            tuple<int, box, box> splits = b.bisect(config.nra_precision);
            int const i = get<0>(splits);
            if (i >= 0) {
                box const & first  = get<1>(splits);
                box const & second = get<2>(splits);
                if (random_bool()) {
                    box_stack.push_back(second);
                    box_stack.push_back(first);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, b, first, second,
                                          config.nra_readable_proof, i);
                    }
                } else {
                    box_stack.push_back(first);
                    box_stack.push_back(second);
                    if (config.nra_proof) {
                        output_split_step(config.nra_proof_out, b, second, first,
                                          config.nra_readable_proof, i);
                    }
                }
            } else {
                config.nra_found_soln++;
                if (config.nra_found_soln >= config.nra_multiple_soln) {
                    break;
                }
                if (config.nra_multiple_soln > 1) {
                    // If --multiple_soln is used
                    output_solution(b, config, config.nra_found_soln);
                }
                solns.push_back(b);
            }
        }
    } while (box_stack.size() > 0);
    if (config.nra_multiple_soln > 1 && solns.size() > 0) {
        return solns.back();
    } else {
        assert(!b.is_empty() || box_stack.size() == 0);
        // cerr << "BEFORE ADJUST_BOUND\n==================\n" << b << "=========================\n\n\n";
        b.adjust_bound(box_stack);
        // cerr << "AFTER  ADJUST_BOUND\n==================\n" << b << "=========================\n\n\n";
        return b;
    }
}

//TODO print proof
void parallel_icp::worker(int tid) {
    //cerr << "worker starting" << endl;
    std::unique_lock<std::mutex> l(lock); //this acquires l
    while (true) {
        if (!found_solution && working > 1 && box_stack.empty()) {
            working -= 1;
            //cerr << tid << " waiting" << endl;
            cv.wait(l, [this]{return found_solution || working == 0 || !box_stack.empty();});
            working += 1;
            //cerr << tid << " woke up" << endl;
        }
        if (found_solution || box_stack.empty()) { 
            //someone has a solution or there is no more work to do
            working -= 1;
            //cerr << tid << " worker done" << endl;
            //cerr << tid << " found_solution = " << found_solution << endl;
            //cerr << tid << " working        = " << working << endl;
            //cerr << tid << " box_stack.size = " << box_stack.size() << endl;
            l.unlock();
            cv.notify_all();
            break;
        } else {
            //fetch some work
            tuple<unsigned, box> branch = box_stack.top();
            box_stack.pop();
            l.unlock();

            unsigned id = get<0>(branch);
            box b = get<1>(branch);
            //cerr << tid << " working on branch: " << id << ", stack: " << box_stack.size() << endl;
            assert(!b.is_empty());

            while (!b.is_empty()) {

                //prune
                try {
                    if (config.nra_use_stat) { config.nra_stat.increase_prune(); }
                    b = ctc.prune(b, config);
                } catch (contractor_exception & e) {
                    // Do nothing
                }

                if (!b.is_empty()) {
                    // split
                    if (config.nra_use_stat) { config.nra_stat.increase_branch(); }
                    tuple<int, box, box> splits = b.bisect(config.nra_precision);
                    int const i = get<0>(splits);
                    if (i >= 0) {
                        //push one branch on the stack and continue with the other
                        b = get<1>(splits);
                        box const & other_branch = get<2>(splits);
                        l.lock();
                        branches += 1;
                        //cerr << tid << " new branch " << branches << endl;
                        box_stack.push(tuple<unsigned,box>(branches,other_branch));
                        l.unlock();
                        cv.notify_all();
                    } else {
                        //we have a solution
                        //cerr << tid << " found a solution" << endl;
                        l.lock();
                        solutions.push(b);
                        if (solutions.size() >= config.nra_multiple_soln) {
                            found_solution = true;
                        }
                        //we keep the lock as we are exiting the inner loop
                        break;
                    }
                } else {
                    l.lock();
                    //cerr << tid << " branch " << id << " done" << endl;
                }

            }

        }
    }
    //l.lock();
    //cerr << tid << " exiting" << endl;
    //l.unlock();
}

box parallel_icp::solve(box b, contractor const & ctc, SMTConfig & config) {
    int nbr_workers = std::thread::hardware_concurrency();
    if (nbr_workers == 0) {
        return naive_icp::solve(b, ctc, config);
    } else {
        parallel_icp p_icp(ctc, config);
        p_icp.working = nbr_workers;
        std::unique_lock<std::mutex> l(p_icp.lock); //this acquires l
        //push the initial box
        //cerr << "1" << endl;
        p_icp.box_stack.push(tuple<unsigned,box>(0,b));
        //cerr << "2" << endl;
        //create the workers
        std::thread workers[nbr_workers];
        for (int i = 0; i < nbr_workers; i++) {
             workers[i] = std::thread([&p_icp,i] { p_icp.worker(i); });
        }
        //cerr << "3" << endl;
        p_icp.cv.wait(l, [&p_icp]{return p_icp.found_solution || (p_icp.working == 0 && p_icp.box_stack.empty());});
        l.unlock();
        for (int i = 0; i < nbr_workers; i++) {
             //cerr << "joining " << i << endl;
             workers[i].join();
        }
        //cerr << "4" << endl;
        //check if there is a solution
        if (p_icp.found_solution) {
            //cerr << "5" << endl;
            box sol = p_icp.solutions.top();
            //cerr << "6" << endl;
            sol.set_bounds(b.get_values());
            //cerr << "7" << endl;
            return sol;
        } else {
            //cerr << "8" << endl;
            b.set_empty();
            //cerr << "9" << endl;
            return b;
        }
    }
}

}  // namespace dreal
