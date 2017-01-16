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
(assert (and (> (- (* (- 6) x1) (* (- 3) x2)) 10) (> (- x3 (* (- 3) x3)) 20) (> (- (- x4) (- x5)) 30)))
(check-sat)
(exit)