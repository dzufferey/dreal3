(set-logic QF_NRA)
(set-info :source | KeYmaera example: exit-simultaneous-different-directions, node 303
Andre Platzer and Edmund M. Clarke. Formal verification of curved flight collision avoidance maneuvers: A case study. In Ana Cavalcanti and Dennis Dams, editors, 16th International Symposium on Formal Methods, FM, Eindhoven, Netherlands, Proceedings, volume 5850 of LNCS, pages 547(- 562.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-const d1 Real)
(declare-const om Real)
(declare-const x2 Real)
(declare-const c2 Real)
(declare-const d2 Real)
(declare-const x1 Real)
(declare-const c1 Real)
(declare-const e1 Real)
(declare-const y2 Real)
(declare-const e2 Real)
(declare-const y1 Real)
(assert (not (=> (and (and (and (= d1 (* (- om) (- x2 c2)) ) (= d2 (* om (- x1 c1)) )) (= e1 (* (- om) (- y2 c2)) )) (= e2 (* om (- y1 c1)) )) (or (= d1 e1 ) (> (+ (* (- d1 e1) (- d1 e1)) (* (- d2 e2) (- d2 e2))) 0. )))))
(check-sat)
(exit)
