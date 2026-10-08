import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.isComplementOfDisjointSupTop
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient

/-!
# Import bundle for the `FrobeniusWith → IsFrobeniusGroup` helpers of area BG

Collects the modules that the auxiliary lemmas around
`Work.BG.c3FrobFrobeniusGroupOfWith` need, so that a delegated lemma can simply
`import Submission.Work.BG.c3FrobWithImports`:

* `Submission.Work.GLUE.Defs` for the vocabulary `Work.GW2.IsFrobeniusWith`;
* `Work.BG.isComplement'_of_disjoint_sup_eq_top_of_normal` (auxiliary complement lemma);
* `Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup` for
  `OddOrder.Isaacs.Ch06.IsFrobeniusGroup` (Isaacs Thm 6.4, subgroup-pair form).
-/
