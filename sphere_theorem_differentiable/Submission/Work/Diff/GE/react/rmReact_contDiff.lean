import Mathlib
import Submission.Work.Diff.GE.fixRmDefs
import Submission.Work.Diff.Evol.Calc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.react

/-- The reaction map `rmReact R = Q R - Xact R` of the fixed-vector curvature evolution is smooth:
it is a finite sum of products of the coordinate projections `R ↦ R i j k l` (with all sums over the
finite types `Fin n`), so `fun_prop` closes it after unfolding `Q`, `Xact` and `ricArr`. -/
theorem rmReact_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.GE.rmReact n) := by
  unfold Work.Diff.GE.rmReact Submission.Diff.Alg.Q Work.Diff.Evol.Xact Work.Diff.Evol.ricArr
  fun_prop

end Work.Diff.GE.react
