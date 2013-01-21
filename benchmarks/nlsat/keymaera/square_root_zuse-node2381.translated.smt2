(set-logic QF_NRA)
(declare-fun puscore2dollarsk!2 () Real)
(declare-fun quscore2dollarsk!1 () Real)
(declare-fun ruscore2dollarsk!0 () Real)
(declare-fun err () Real)
(declare-fun a () Real)
(assert (>= (+ (* 2.0 ruscore2dollarsk!0)
               (* (- 2.0) quscore2dollarsk!1)
               (* (- 1.0) puscore2dollarsk!2))
            0.0))
(assert (>= (* 2.0 puscore2dollarsk!2 ruscore2dollarsk!0) err))
(assert (= a
           (+ (* quscore2dollarsk!1 quscore2dollarsk!1)
              (* 2.0 puscore2dollarsk!2 ruscore2dollarsk!0))))
(assert (not (= a
                (+ (* (+ quscore2dollarsk!1 puscore2dollarsk!2)
                      (+ quscore2dollarsk!1 puscore2dollarsk!2))
                   (* puscore2dollarsk!2
                      (+ (* 2.0 ruscore2dollarsk!0)
                         (* (- 2.0) quscore2dollarsk!1)
                         (* (- 1.0) puscore2dollarsk!2)))))))
(check-sat)
(exit)
