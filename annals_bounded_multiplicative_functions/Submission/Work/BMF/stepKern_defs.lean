import Submission.Commons.Analysis.Complex.exists_perron_formula_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Re-export of the truncated Perron step kernel `Commons.Analysis.Complex.stepKern`

This thin module exists so that helpers in `Submission.Work.BMF.*` can be stated in terms of
`Commons.Analysis.Complex.stepKern` (and its deviation bound `perronStep_deviation_pos`) while
depending only on a module under `Submission/Work/`, as the lemma-request plumbing requires.
-/
