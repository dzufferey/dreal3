(set-logic QF_NRA)
(set-info :source |
SMT script generated by Ultimate Automizer [1,2].
Ultimate Automizer is a software verifier for C programs that implements an
automata-based approach [3].
The commands in this SMT scripts are used for a constraint-based synthesis
of invariants [4].

2016-04-30, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)


[1] http://http://ultimate.informatik.uni-freiburg.de/automizer/
[2] Matthias Heizmann, Daniel Dietsch, Marius Greitschus, Jan Leike,
Betim Musa, Claus Schätzle, Andreas Podelski: Ultimate Automizer with
Two-track Proofs - (Competition Contribution). TACAS 2016: 950-953
[3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski: Software Model
Checking for People Who Love Automata. CAV 2013:36-52
[4] Michael Colon, Sriram Sankaranarayanan, Henny Sipma: Linear Invariant
Generation Using Non-linear Constraint Solving. CAV 2003: 420-432

|)
(set-info :smt-lib-version 2.5)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun liipp_0_c () Real)
(declare-fun liipp_0__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_0__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_0__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_0__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_0__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_0__product__global_next () Real)
(declare-fun liipp_1_c () Real)
(declare-fun liipp_1__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_1__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_1__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_1__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_1__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_1__product__global_next () Real)
(declare-fun liipp_2_c () Real)
(declare-fun liipp_2__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_2__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_2__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_2__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_2__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_2__product__global_next () Real)
(declare-fun liipp_3_c () Real)
(declare-fun liipp_3__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_3__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_3__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_3__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_3__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_3__product__global_next () Real)
(declare-fun liipp_4_c () Real)
(declare-fun liipp_4__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_4__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_4__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_4__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_4__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_4__product__global_next () Real)
(declare-fun liipp_5_c () Real)
(declare-fun liipp_5__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_5__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_5__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_5__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_5__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_5__product__global_next () Real)
(declare-fun liipp_6_c () Real)
(declare-fun liipp_6__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_6__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_6__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_6__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_6__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_6__product__global_next () Real)
(declare-fun liipp_7_c () Real)
(declare-fun liipp_7__product__local__threadpooling_working_1 () Real)
(declare-fun liipp_7__product__local__threadpooling_working_0 () Real)
(declare-fun liipp_7__product__local__threadpooling_begin_0 () Real)
(declare-fun liipp_7__product__local__threadpooling_end_0 () Real)
(declare-fun liipp_7__product__local__threadpooling_i_0 () Real)
(declare-fun liipp_7__product__global_next () Real)
(declare-fun liipp_8_replace_0 () Real)
(declare-fun liipp_8_replace_1 () Real)
(declare-fun liipp_8_replace_2 () Real)
(declare-fun liipp_8_replace_3 () Real)
(declare-fun liipp_8_replace_4 () Real)
(declare-fun liipp_8_replace_5 () Real)
(declare-fun liipp_9_replace_0 () Real)
(declare-fun liipp_9_replace_1 () Real)
(declare-fun liipp_9_replace_2 () Real)
(declare-fun liipp_9_replace_3 () Real)
(declare-fun liipp_9_replace_4 () Real)
(declare-fun liipp_9_replace_5 () Real)
(declare-fun liipp_10_replace_0 () Real)
(declare-fun liipp_10_replace_1 () Real)
(declare-fun liipp_10_replace_2 () Real)
(declare-fun motzkin_3197_0 () Real)
(declare-fun motzkin_3197_1 () Real)
(declare-fun motzkin_3197_2 () Real)
(declare-fun motzkin_3197_3 () Real)
(declare-fun motzkin_3197_4 () Real)
(declare-fun motzkin_3197_5 () Real)
(declare-fun motzkin_3198_0 () Real)
(declare-fun motzkin_3198_1 () Real)
(declare-fun motzkin_3198_2 () Real)
(declare-fun motzkin_3198_3 () Real)
(declare-fun motzkin_3198_4 () Real)
(declare-fun motzkin_3198_5 () Real)
(assert (and (>= motzkin_3197_0 0.0) (>= motzkin_3197_1 0.0) (>= motzkin_3197_2 0.0) (>= motzkin_3197_3 0.0) (>= motzkin_3197_4 0.0) (>= motzkin_3197_5 0.0) (= (+ motzkin_3197_0 (* motzkin_3197_1 (- 1.0)) (* motzkin_3197_5 (+ (* (- 1.0) liipp_6__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ motzkin_3197_2 (* motzkin_3197_5 (+ (* (- 1.0) liipp_6__product__global_next) 0.0))) 0.0) (= (+ motzkin_3197_3 (* motzkin_3197_4 (- 1.0)) (* motzkin_3197_5 (+ (* (- 1.0) liipp_6__product__local__threadpooling_working_0) 0.0))) 0.0) (= (* motzkin_3197_5 (+ (* (- 1.0) liipp_6__product__local__threadpooling_end_0) 0.0)) 0.0) (= (* motzkin_3197_5 (+ (* (- 1.0) liipp_6__product__local__threadpooling_begin_0) 0.0)) 0.0) (= (* motzkin_3197_5 (+ (* (- 1.0) liipp_6__product__local__threadpooling_i_0) 0.0)) 0.0) (<= (+ motzkin_3197_0 (* motzkin_3197_1 (- 1.0)) (* motzkin_3197_2 (- 1.0)) motzkin_3197_3 (* motzkin_3197_4 (- 1.0)) (* motzkin_3197_5 (+ (* (- 1.0) liipp_6_c) 0.0))) 0.0) (or (< (+ motzkin_3197_0 (* motzkin_3197_1 (- 1.0)) (* motzkin_3197_2 (- 1.0)) motzkin_3197_3 (* motzkin_3197_4 (- 1.0)) (* motzkin_3197_5 (+ (* (- 1.0) liipp_6_c) 0.0))) 0.0) (> 0.0 0.0)) (>= motzkin_3198_0 0.0) (>= motzkin_3198_1 0.0) (>= motzkin_3198_2 0.0) (>= motzkin_3198_3 0.0) (>= motzkin_3198_4 0.0) (>= motzkin_3198_5 0.0) (= (+ motzkin_3198_0 (* motzkin_3198_1 (- 1.0)) (* motzkin_3198_5 (+ (* (- 1.0) liipp_7__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ motzkin_3198_2 (* motzkin_3198_5 (+ (* (- 1.0) liipp_7__product__global_next) 0.0))) 0.0) (= (+ motzkin_3198_3 (* motzkin_3198_4 (- 1.0)) (* motzkin_3198_5 (+ (* (- 1.0) liipp_7__product__local__threadpooling_working_0) 0.0))) 0.0) (= (* motzkin_3198_5 (+ (* (- 1.0) liipp_7__product__local__threadpooling_end_0) 0.0)) 0.0) (= (* motzkin_3198_5 (+ (* (- 1.0) liipp_7__product__local__threadpooling_begin_0) 0.0)) 0.0) (= (* motzkin_3198_5 (+ (* (- 1.0) liipp_7__product__local__threadpooling_i_0) 0.0)) 0.0) (<= (+ motzkin_3198_0 (* motzkin_3198_1 (- 1.0)) (* motzkin_3198_2 (- 1.0)) motzkin_3198_3 (* motzkin_3198_4 (- 1.0)) (* motzkin_3198_5 (+ (* (- 1.0) liipp_7_c) 0.0))) 0.0) (or (< (+ motzkin_3198_0 (* motzkin_3198_1 (- 1.0)) (* motzkin_3198_2 (- 1.0)) motzkin_3198_3 (* motzkin_3198_4 (- 1.0))) 0.0) (> motzkin_3198_5 0.0))))
(declare-fun liipp_11_replace_0 () Real)
(declare-fun liipp_11_replace_1 () Real)
(declare-fun motzkin_3199_0 () Real)
(declare-fun motzkin_3199_1 () Real)
(declare-fun motzkin_3199_2 () Real)
(declare-fun motzkin_3199_3 () Real)
(declare-fun motzkin_3199_4 () Real)
(declare-fun motzkin_3199_5 () Real)
(declare-fun motzkin_3199_6 () Real)
(declare-fun motzkin_3199_7 () Real)
(declare-fun motzkin_3199_8 () Real)
(declare-fun motzkin_3199_9 () Real)
(declare-fun motzkin_3199_10 () Real)
(declare-fun motzkin_3200_0 () Real)
(declare-fun motzkin_3200_1 () Real)
(declare-fun motzkin_3200_2 () Real)
(declare-fun motzkin_3200_3 () Real)
(declare-fun motzkin_3200_4 () Real)
(declare-fun motzkin_3200_5 () Real)
(declare-fun motzkin_3200_6 () Real)
(declare-fun motzkin_3200_7 () Real)
(declare-fun motzkin_3200_8 () Real)
(declare-fun motzkin_3200_9 () Real)
(declare-fun motzkin_3200_10 () Real)
(assert (and (>= motzkin_3199_0 0.0) (>= motzkin_3199_1 0.0) (>= motzkin_3199_2 0.0) (>= motzkin_3199_3 0.0) (>= motzkin_3199_4 0.0) (>= motzkin_3199_5 0.0) (>= motzkin_3199_6 0.0) (>= motzkin_3199_7 0.0) (>= motzkin_3199_8 0.0) (>= motzkin_3199_9 0.0) (>= motzkin_3199_10 0.0) (= (+ (* motzkin_3199_0 (- 1.0)) motzkin_3199_1 (* motzkin_3199_8 (+ (* (- 1.0) liipp_4__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ motzkin_3199_0 (* motzkin_3199_1 (- 1.0)) motzkin_3199_6 (* motzkin_3199_7 (- 1.0)) (* motzkin_3199_8 (+ (* (- 1.0) liipp_4__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3199_2 (- 1.0)) motzkin_3199_3 motzkin_3199_4 (* motzkin_3199_5 (- 1.0)) (* motzkin_3199_8 (+ (* (- 1.0) liipp_4__product__global_next) 0.0))) 0.0) (= (+ motzkin_3199_2 (* motzkin_3199_3 (- 1.0)) (* motzkin_3199_6 (- 1.0)) motzkin_3199_7 (* motzkin_3199_9 (+ (* 1.0 liipp_6__product__global_next) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7__product__global_next) 0.0))) 0.0) (= (+ (* motzkin_3199_4 (- 1.0)) motzkin_3199_5 (* motzkin_3199_8 (+ (* (- 1.0) liipp_4__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3199_8 (+ (* (- 1.0) liipp_4__product__local__threadpooling_working_1) 0.0)) (* motzkin_3199_9 (+ (* 1.0 liipp_6__product__local__threadpooling_working_1) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3199_8 (+ (* (- 1.0) liipp_4__product__local__threadpooling_working_0) 0.0)) (* motzkin_3199_9 (+ (* 1.0 liipp_6__product__local__threadpooling_working_0) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3199_9 (+ (* 1.0 liipp_6__product__local__threadpooling_end_0) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3199_9 (+ (* 1.0 liipp_6__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3199_9 (+ (* 1.0 liipp_6__product__local__threadpooling_i_0) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7__product__local__threadpooling_i_0) 0.0))) 0.0) (<= (+ motzkin_3199_2 (* motzkin_3199_3 (- 1.0)) (* motzkin_3199_8 (+ (* (- 1.0) liipp_4_c) 0.0)) (* motzkin_3199_9 (+ (* 1.0 liipp_6_c) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7_c) 0.0))) 0.0) (or (< (+ motzkin_3199_2 (* motzkin_3199_3 (- 1.0)) (* motzkin_3199_8 (+ (* (- 1.0) liipp_4_c) 0.0)) (* motzkin_3199_10 (+ (* 1.0 liipp_7_c) 0.0))) 0.0) (> motzkin_3199_9 0.0)) (>= motzkin_3200_0 0.0) (>= motzkin_3200_1 0.0) (>= motzkin_3200_2 0.0) (>= motzkin_3200_3 0.0) (>= motzkin_3200_4 0.0) (>= motzkin_3200_5 0.0) (>= motzkin_3200_6 0.0) (>= motzkin_3200_7 0.0) (>= motzkin_3200_8 0.0) (>= motzkin_3200_9 0.0) (>= motzkin_3200_10 0.0) (= (+ (* motzkin_3200_0 (- 1.0)) motzkin_3200_1 (* motzkin_3200_8 (+ (* (- 1.0) liipp_5__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ motzkin_3200_0 (* motzkin_3200_1 (- 1.0)) motzkin_3200_6 (* motzkin_3200_7 (- 1.0)) (* motzkin_3200_8 (+ (* (- 1.0) liipp_5__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3200_2 (- 1.0)) motzkin_3200_3 motzkin_3200_4 (* motzkin_3200_5 (- 1.0)) (* motzkin_3200_8 (+ (* (- 1.0) liipp_5__product__global_next) 0.0))) 0.0) (= (+ motzkin_3200_2 (* motzkin_3200_3 (- 1.0)) (* motzkin_3200_6 (- 1.0)) motzkin_3200_7 (* motzkin_3200_9 (+ (* 1.0 liipp_6__product__global_next) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7__product__global_next) 0.0))) 0.0) (= (+ (* motzkin_3200_4 (- 1.0)) motzkin_3200_5 (* motzkin_3200_8 (+ (* (- 1.0) liipp_5__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3200_8 (+ (* (- 1.0) liipp_5__product__local__threadpooling_working_1) 0.0)) (* motzkin_3200_9 (+ (* 1.0 liipp_6__product__local__threadpooling_working_1) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3200_8 (+ (* (- 1.0) liipp_5__product__local__threadpooling_working_0) 0.0)) (* motzkin_3200_9 (+ (* 1.0 liipp_6__product__local__threadpooling_working_0) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3200_9 (+ (* 1.0 liipp_6__product__local__threadpooling_end_0) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3200_9 (+ (* 1.0 liipp_6__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3200_9 (+ (* 1.0 liipp_6__product__local__threadpooling_i_0) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7__product__local__threadpooling_i_0) 0.0))) 0.0) (<= (+ motzkin_3200_2 (* motzkin_3200_3 (- 1.0)) (* motzkin_3200_8 (+ (* (- 1.0) liipp_5_c) 0.0)) (* motzkin_3200_9 (+ (* 1.0 liipp_6_c) 0.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7_c) 0.0))) 0.0) (or (< (+ motzkin_3200_2 (* motzkin_3200_3 (- 1.0)) (* motzkin_3200_10 (+ (* 1.0 liipp_7_c) 0.0))) 0.0) (> (+ motzkin_3200_8 motzkin_3200_9) 0.0))))
(declare-fun liipp_12_replace_0 () Real)
(declare-fun liipp_12_replace_1 () Real)
(declare-fun liipp_12_replace_2 () Real)
(declare-fun liipp_12_replace_3 () Real)
(declare-fun motzkin_3201_0 () Real)
(declare-fun motzkin_3201_1 () Real)
(declare-fun motzkin_3201_2 () Real)
(declare-fun motzkin_3201_3 () Real)
(declare-fun motzkin_3202_0 () Real)
(declare-fun motzkin_3202_1 () Real)
(declare-fun motzkin_3202_2 () Real)
(declare-fun motzkin_3202_3 () Real)
(assert (and (>= motzkin_3201_0 0.0) (>= motzkin_3201_1 0.0) (>= motzkin_3201_2 0.0) (>= motzkin_3201_3 0.0) (= (+ (* motzkin_3201_0 (- 1.0)) (* motzkin_3201_1 (+ (* (- 1.0) liipp_2__product__local__threadpooling_i_0) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4__product__local__threadpooling_i_0) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ motzkin_3201_0 (* motzkin_3201_1 (+ (* (- 1.0) liipp_2__product__local__threadpooling_end_0) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4__product__local__threadpooling_end_0) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3201_1 (+ (* (- 1.0) liipp_2__product__local__threadpooling_working_1) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4__product__local__threadpooling_working_1) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3201_1 (+ (* (- 1.0) liipp_2__product__local__threadpooling_working_0) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4__product__local__threadpooling_working_0) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3201_1 (+ (* (- 1.0) liipp_2__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3201_1 (+ (* (- 1.0) liipp_2__product__global_next) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4__product__global_next) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5__product__global_next) 0.0))) 0.0) (<= (+ (* motzkin_3201_0 (- 1.0)) (* motzkin_3201_1 (+ (* (- 1.0) liipp_2_c) 0.0)) (* motzkin_3201_2 (+ (* 1.0 liipp_4_c) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5_c) 0.0))) 0.0) (or (< (+ (* motzkin_3201_0 (- 1.0)) (* motzkin_3201_1 (+ (* (- 1.0) liipp_2_c) 0.0)) (* motzkin_3201_3 (+ (* 1.0 liipp_5_c) 0.0))) 0.0) (> motzkin_3201_2 0.0)) (>= motzkin_3202_0 0.0) (>= motzkin_3202_1 0.0) (>= motzkin_3202_2 0.0) (>= motzkin_3202_3 0.0) (= (+ (* motzkin_3202_0 (- 1.0)) (* motzkin_3202_1 (+ (* (- 1.0) liipp_3__product__local__threadpooling_i_0) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4__product__local__threadpooling_i_0) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ motzkin_3202_0 (* motzkin_3202_1 (+ (* (- 1.0) liipp_3__product__local__threadpooling_end_0) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4__product__local__threadpooling_end_0) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3202_1 (+ (* (- 1.0) liipp_3__product__local__threadpooling_working_1) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4__product__local__threadpooling_working_1) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3202_1 (+ (* (- 1.0) liipp_3__product__local__threadpooling_working_0) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4__product__local__threadpooling_working_0) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3202_1 (+ (* (- 1.0) liipp_3__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3202_1 (+ (* (- 1.0) liipp_3__product__global_next) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4__product__global_next) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5__product__global_next) 0.0))) 0.0) (<= (+ (* motzkin_3202_0 (- 1.0)) (* motzkin_3202_1 (+ (* (- 1.0) liipp_3_c) 0.0)) (* motzkin_3202_2 (+ (* 1.0 liipp_4_c) 0.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5_c) 0.0))) 0.0) (or (< (+ (* motzkin_3202_0 (- 1.0)) (* motzkin_3202_3 (+ (* 1.0 liipp_5_c) 0.0))) 0.0) (> (+ motzkin_3202_1 motzkin_3202_2) 0.0))))
(declare-fun liipp_13_replace_0 () Real)
(declare-fun liipp_13_replace_1 () Real)
(declare-fun liipp_13_replace_2 () Real)
(declare-fun liipp_13_replace_3 () Real)
(declare-fun motzkin_3203_0 () Real)
(declare-fun motzkin_3203_1 () Real)
(declare-fun motzkin_3203_2 () Real)
(declare-fun motzkin_3203_3 () Real)
(declare-fun motzkin_3203_4 () Real)
(declare-fun motzkin_3204_0 () Real)
(declare-fun motzkin_3204_1 () Real)
(declare-fun motzkin_3204_2 () Real)
(declare-fun motzkin_3204_3 () Real)
(declare-fun motzkin_3204_4 () Real)
(assert (and (>= motzkin_3203_0 0.0) (>= motzkin_3203_1 0.0) (>= motzkin_3203_2 0.0) (>= motzkin_3203_3 0.0) (>= motzkin_3203_4 0.0) (= (+ motzkin_3203_0 (* motzkin_3203_1 (- 1.0)) (* motzkin_3203_2 (+ (* (- 1.0) liipp_0__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3203_0 (- 1.0)) motzkin_3203_1 (* motzkin_3203_2 (+ (* (- 1.0) liipp_0__product__local__threadpooling_i_0) 0.0)) (* motzkin_3203_3 (+ (* 1.0 liipp_2__product__local__threadpooling_i_0) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ (* motzkin_3203_2 (+ (* (- 1.0) liipp_0__product__local__threadpooling_working_1) 0.0)) (* motzkin_3203_3 (+ (* 1.0 liipp_2__product__local__threadpooling_working_1) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3203_2 (+ (* (- 1.0) liipp_0__product__local__threadpooling_end_0) 0.0)) (* motzkin_3203_3 (+ (* 1.0 liipp_2__product__local__threadpooling_end_0) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3203_2 (+ (* (- 1.0) liipp_0__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3203_3 (+ (* 1.0 liipp_2__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3203_2 (+ (* (- 1.0) liipp_0__product__global_next) 0.0)) (* motzkin_3203_3 (+ (* 1.0 liipp_2__product__global_next) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3__product__global_next) 0.0))) 0.0) (= (+ (* motzkin_3203_3 (+ (* 1.0 liipp_2__product__local__threadpooling_working_0) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3__product__local__threadpooling_working_0) 0.0))) 0.0) (<= (+ (* motzkin_3203_2 (+ (* (- 1.0) liipp_0_c) 0.0)) (* motzkin_3203_3 (+ (* 1.0 liipp_2_c) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3_c) 0.0))) 0.0) (or (< (+ (* motzkin_3203_2 (+ (* (- 1.0) liipp_0_c) 0.0)) (* motzkin_3203_4 (+ (* 1.0 liipp_3_c) 0.0))) 0.0) (> motzkin_3203_3 0.0)) (>= motzkin_3204_0 0.0) (>= motzkin_3204_1 0.0) (>= motzkin_3204_2 0.0) (>= motzkin_3204_3 0.0) (>= motzkin_3204_4 0.0) (= (+ motzkin_3204_0 (* motzkin_3204_1 (- 1.0)) (* motzkin_3204_2 (+ (* (- 1.0) liipp_1__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3204_0 (- 1.0)) motzkin_3204_1 (* motzkin_3204_2 (+ (* (- 1.0) liipp_1__product__local__threadpooling_i_0) 0.0)) (* motzkin_3204_3 (+ (* 1.0 liipp_2__product__local__threadpooling_i_0) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ (* motzkin_3204_2 (+ (* (- 1.0) liipp_1__product__local__threadpooling_working_1) 0.0)) (* motzkin_3204_3 (+ (* 1.0 liipp_2__product__local__threadpooling_working_1) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3204_2 (+ (* (- 1.0) liipp_1__product__local__threadpooling_end_0) 0.0)) (* motzkin_3204_3 (+ (* 1.0 liipp_2__product__local__threadpooling_end_0) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3204_2 (+ (* (- 1.0) liipp_1__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3204_3 (+ (* 1.0 liipp_2__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3204_2 (+ (* (- 1.0) liipp_1__product__global_next) 0.0)) (* motzkin_3204_3 (+ (* 1.0 liipp_2__product__global_next) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3__product__global_next) 0.0))) 0.0) (= (+ (* motzkin_3204_3 (+ (* 1.0 liipp_2__product__local__threadpooling_working_0) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3__product__local__threadpooling_working_0) 0.0))) 0.0) (<= (+ (* motzkin_3204_2 (+ (* (- 1.0) liipp_1_c) 0.0)) (* motzkin_3204_3 (+ (* 1.0 liipp_2_c) 0.0)) (* motzkin_3204_4 (+ (* 1.0 liipp_3_c) 0.0))) 0.0) (or (< (* motzkin_3204_4 (+ (* 1.0 liipp_3_c) 0.0)) 0.0) (> (+ motzkin_3204_2 motzkin_3204_3) 0.0))))
(declare-fun liipp_14_replace_0 () Real)
(declare-fun liipp_14_replace_1 () Real)
(declare-fun liipp_14_replace_2 () Real)
(declare-fun liipp_14_replace_3 () Real)
(declare-fun motzkin_3205_0 () Real)
(declare-fun motzkin_3205_1 () Real)
(declare-fun motzkin_3205_2 () Real)
(declare-fun motzkin_3205_3 () Real)
(assert (and (>= motzkin_3205_0 0.0) (>= motzkin_3205_1 0.0) (>= motzkin_3205_2 0.0) (>= motzkin_3205_3 0.0) (= (+ motzkin_3205_0 (* motzkin_3205_1 (- 1.0)) (* motzkin_3205_2 (+ (* 1.0 liipp_0__product__local__threadpooling_working_1) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1__product__local__threadpooling_working_1) 0.0))) 0.0) (= (+ (* motzkin_3205_0 (- 1.0)) motzkin_3205_1 (* motzkin_3205_2 (+ (* 1.0 liipp_0__product__local__threadpooling_working_0) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1__product__local__threadpooling_working_0) 0.0))) 0.0) (= (+ (* motzkin_3205_2 (+ (* 1.0 liipp_0__product__local__threadpooling_end_0) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1__product__local__threadpooling_end_0) 0.0))) 0.0) (= (+ (* motzkin_3205_2 (+ (* 1.0 liipp_0__product__local__threadpooling_begin_0) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1__product__local__threadpooling_begin_0) 0.0))) 0.0) (= (+ (* motzkin_3205_2 (+ (* 1.0 liipp_0__product__local__threadpooling_i_0) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1__product__local__threadpooling_i_0) 0.0))) 0.0) (= (+ (* motzkin_3205_2 (+ (* 1.0 liipp_0__product__global_next) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1__product__global_next) 0.0))) 0.0) (<= (+ (* motzkin_3205_2 (+ (* 1.0 liipp_0_c) 0.0)) (* motzkin_3205_3 (+ (* 1.0 liipp_1_c) 0.0))) 0.0) (or (< (* motzkin_3205_3 (+ (* 1.0 liipp_1_c) 0.0)) 0.0) (> motzkin_3205_2 0.0))))
(check-sat)
(exit)