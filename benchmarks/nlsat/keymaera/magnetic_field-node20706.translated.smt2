(set-logic QF_NRA)
(declare-fun xuscore3dollarsk!1 () Real)
(declare-fun a () Real)
(declare-fun vyuscore3dollarsk!3 () Real)
(declare-fun vxuscore3dollarsk!2 () Real)
(declare-fun buscore2dollarsk!5 () Real)
(declare-fun yuscore3dollarsk!0 () Real)
(declare-fun stateuscore2dollarsk!4 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(declare-fun vyuscore2dollarsk!6 () Real)
(assert (= vyuscore3dollarsk!3 (+ (- 2.0) (* a (+ (- 2.0) xuscore3dollarsk!1)))))
(assert (= (+ (* vxuscore3dollarsk!2 vxuscore3dollarsk!2)
              (* vyuscore3dollarsk!3 vyuscore3dollarsk!3))
           8.0))
(assert (= vxuscore3dollarsk!2
           (+ 2.0
              (* (- 1.0) a (+ 2.0 yuscore3dollarsk!0))
              (* 4.0 buscore2dollarsk!5 (+ 1.0 (* (- 1.0) a))))))
(assert (= stateuscore2dollarsk!4 2.0))
(assert (= vyuscore3dollarsk!3 (- 2.0)))
(assert (= vxuscore3dollarsk!2 2.0))
(assert (= (* a (+ xuscore3dollarsk!1 yuscore3dollarsk!0))
           (+ (* 4.0 buscore2dollarsk!5) (* (- 4.0) a buscore2dollarsk!5))))
(assert (= stateuscore2dollarsk!4 1.0))
(assert (= stateuscore2dollarsk!4 0.0))
(assert (= vx 2.0))
(assert (= vy (- 2.0)))
(assert (= x 0.0))
(assert (= y 0.0))
(assert (= b 0.0))
(assert (not (= vyuscore2dollarsk!6 (- 2.0))))
(assert (not (= (* a (+ xuscore3dollarsk!1 (* (- 1.0) yuscore3dollarsk!0)))
                (* (+ (- 4.0) (* (- 4.0) buscore2dollarsk!5))
                   (+ 1.0 (* (- 1.0) a))))))
(check-sat)
(exit)
