(set-logic QF_LRA)
(set-info :source | SMT-COMP'06 organizers |)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(set-info :notes |This benchmark is designed to check if the DP supports bignumbers.|)
(declare-fun y2 () Real)
(declare-fun y99 () Real)
(assert (and (> (* (- 2) y2) 6) (<= (* (/ (- 2) 100) y99) 50)))
(check-sat)
(exit)
