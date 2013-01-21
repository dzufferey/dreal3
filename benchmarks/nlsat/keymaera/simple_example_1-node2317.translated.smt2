(set-logic QF_NRA)
(declare-fun e () Real)
(declare-fun buscore2dollarsk!2 () Real)
(declare-fun auscore2dollarsk!3 () Real)
(declare-fun duscore2dollarsk!0 () Real)
(declare-fun cuscore2dollarsk!1 () Real)
(assert (= e 0.0))
(assert (= (* 2.0 auscore2dollarsk!3) buscore2dollarsk!2))
(assert (= cuscore2dollarsk!1 duscore2dollarsk!0))
(assert (not (= auscore2dollarsk!3 (* (/ 1.0 2.0) buscore2dollarsk!2))))
(check-sat)
(exit)
