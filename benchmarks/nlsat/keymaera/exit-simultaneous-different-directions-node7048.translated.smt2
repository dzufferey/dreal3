(set-logic QF_NRA)
(declare-fun c2 () Real)
(declare-fun x2 () Real)
(declare-fun om () Real)
(declare-fun d1 () Real)
(declare-fun c1 () Real)
(declare-fun x1 () Real)
(declare-fun d2 () Real)
(declare-fun y2 () Real)
(declare-fun e1 () Real)
(declare-fun y1 () Real)
(declare-fun e2 () Real)
(declare-fun e2uscore1dollarsk!1 () Real)
(declare-fun d2uscore1dollarsk!3 () Real)
(declare-fun e1uscore1dollarsk!0 () Real)
(declare-fun d1uscore1dollarsk!2 () Real)
(assert (= d1 (* (- 1.0) om (+ x2 (* (- 1.0) c2)))))
(assert (= d2 (* om (+ x1 (* (- 1.0) c1)))))
(assert (= e1 (* (- 1.0) om (+ y2 (* (- 1.0) c2)))))
(assert (= e2 (* om (+ y1 (* (- 1.0) c1)))))
(assert (not (= d1 e1)))
(assert (not (>= (+ (* (+ (* 2.0 d2uscore1dollarsk!3) (* (- 2.0) e2uscore1dollarsk!1))
                       (+ (* d1uscore1dollarsk!2 om)
                          (* (- 1.0) e1uscore1dollarsk!0 om)))
                    (* (+ (* 2.0 d1uscore1dollarsk!2)
                          (* (- 2.0) e1uscore1dollarsk!0))
                       (+ (* (- 1.0) d2uscore1dollarsk!3 om)
                          (* e2uscore1dollarsk!1 om))))
                 0.0)))
(check-sat)
(exit)
