(set-logic QF_LRA)
(set-info :source | SMT-COMP'06 organizers |)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(set-info :notes |This benchmark is designed to check if the DP supports bignumbers.|)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(assert (and (and (and (>= (- x1 x2) 86) (>= (- x2 x3) 99)) (>= (- x4 x1) 92)) (and (and (>= (- x5 x6) 94) (>= (- x5 x7) 98)) (>= (- x4 x5) 63))))
(check-sat)
(exit)
