(set-logic QF_NRA)
(declare-fun xuscore10dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun vyuscore10dollarsk!3 () Real)
(declare-fun vxuscore10dollarsk!2 () Real)
(declare-fun buscore2dollarsk!5 () Real)
(declare-fun yuscore10dollarsk!0 () Real)
(declare-fun stateuscore2dollarsk!4 () Real)
(declare-fun vyuscore2dollarsk!9 () Real)
(declare-fun vxuscore2dollarsk!8 () Real)
(declare-fun yuscore2dollarsk!6 () Real)
(declare-fun xuscore2dollarsk!7 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(assert (= vyuscore10dollarsk!3 (+ (- 2.0) (* a (+ (- 2.0) xuscore10dollarsk!1)))))
(assert (= (+ (* vxuscore10dollarsk!2 vxuscore10dollarsk!2)
              (* vyuscore10dollarsk!3 vyuscore10dollarsk!3))
           8.0))
(assert (= vxuscore10dollarsk!2
           (+ 2.0
              (* (- 1.0) a (+ 2.0 yuscore10dollarsk!0))
              (* 4.0 buscore2dollarsk!5 (+ 1.0 (* (- 1.0) a))))))
(assert (= stateuscore2dollarsk!4 2.0))
(assert (= vyuscore10dollarsk!3 (- 2.0)))
(assert (= vxuscore10dollarsk!2 2.0))
(assert (= (* a (+ xuscore10dollarsk!1 yuscore10dollarsk!0))
           (+ (* 4.0 buscore2dollarsk!5) (* (- 4.0) a buscore2dollarsk!5))))
(assert (= stateuscore2dollarsk!4 1.0))
(assert (= vyuscore2dollarsk!9 (- 2.0)))
(assert (= vxuscore2dollarsk!8 (- 2.0)))
(assert (= (* a (+ xuscore2dollarsk!7 (* (- 1.0) yuscore2dollarsk!6)))
           (* (+ (- 4.0) (* (- 4.0) buscore2dollarsk!5)) (+ 1.0 (* (- 1.0) a)))))
(assert (= vx 2.0))
(assert (= vy (- 2.0)))
(assert (= x 0.0))
(assert (= y 0.0))
(assert (= b 0.0))
(assert (not (= vxuscore10dollarsk!2 (- 2.0))))
(check-sat)
(exit)
