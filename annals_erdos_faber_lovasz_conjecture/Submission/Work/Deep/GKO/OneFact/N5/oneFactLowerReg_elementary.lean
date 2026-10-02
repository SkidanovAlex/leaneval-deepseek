import Submission.Work.Deep.GKO.OneFact.N5.Asm.Main
import Submission.Work.Deep.GKO.OneFact.N5.Asm.threshold_arith
import Submission.Work.Deep.GKO.OneFact.N5.Asm.regular_iSup_matchings
import Submission.Work.Deep.GKO.OneFact.N5.Asm.card_neighborSet_iSup_le_ncard
import Submission.Work.Deep.GKO.OneFact.N5.completeAllClasses

/-!
# N5: the elementary one-factorization route, assembled

`Work.Deep.GKO.OneFact.N5.Asm.main_of_children` (in `Asm/Main.lean`) proves
`Work.Deep.GKO.OneFactLowerRegStatement` from the pieces of the elementary route, taken there
as hypotheses.  This file discharges them:

* `Asm.threshold_arith` — the numerical side conditions (`ArithOK`) hold for `n` large enough;
* `Asm.regular_iSup_matchings` — the union of pairwise edge-disjoint perfect matchings of `G` is
  regular of degree the number of matchings and has itself a one-factorization;
* `Asm.card_neighborSet_iSup_le_ncard` — the degree in a union of matchings is at most the number
  of matchings meeting the vertex;
* `Work.Deep.GKO.OneFact.N5.completeAllClasses` — the iterative completion of the good Vizing
  classes (nodes N5b/N5c).
-/

namespace Work.Deep.GKO.OneFact.N5

theorem oneFactLowerReg_elementary : Work.Deep.GKO.OneFactLowerRegStatement :=
  Asm.main_of_children Asm.threshold_arith Asm.regular_iSup_matchings
    Asm.card_neighborSet_iSup_le_ncard Work.Deep.GKO.OneFact.N5.completeAllClasses

end Work.Deep.GKO.OneFact.N5
