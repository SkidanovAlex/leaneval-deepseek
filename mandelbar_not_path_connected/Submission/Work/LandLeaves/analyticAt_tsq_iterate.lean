import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- The holomorphic second iterate `Tsq c z = (z² + c̄)² + c` of the tricorn map is analytic
everywhere: it is a polynomial function of `z`. -/
theorem analyticAt_Tsq (c z : ℂ) : AnalyticAt ℂ (Work.Landing.Tsq c) z := by
  change AnalyticAt ℂ (fun z => (z ^ 2 + star c) ^ 2 + c) z
  fun_prop

/-- Every iterate of the holomorphic second return map `Tsq c` is analytic everywhere. -/
theorem analyticAt_tsq_iterate (c : ℂ) (k : ℕ) (z : ℂ) :
    AnalyticAt ℂ ((Work.Landing.Tsq c)^[k]) z := by
  induction k generalizing z with
  | zero => simpa using analyticAt_id (z := z)
  | succ k ih =>
    rw [Function.iterate_succ]
    exact (ih (Work.Landing.Tsq c z)).comp (analyticAt_Tsq c z)

end Work.LandLeaves
