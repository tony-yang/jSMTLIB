(set-logic QF_LRA)
(set-info :source | SMT-COMP'06 organizers |)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(set-info :notes |This benchmark is designed to check if the DP supports bignumbers.|)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(assert (< (+ 6 (* 5 x3) 20) (+ (- x1) (* 3 x2) (- 5))))
(check-sat)
(exit)