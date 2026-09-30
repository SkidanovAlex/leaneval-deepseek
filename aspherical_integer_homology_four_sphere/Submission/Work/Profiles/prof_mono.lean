import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Profiles

open scoped ContDiff

open MeasureTheory

theorem prof_mono {F η : ℝ → ℝ} (hF : Monotone F) (hFc : Continuous F) (hη : ∀ t, 0 ≤ η t)
    (hηcont : Continuous η) (hηc : HasCompactSupport η) : Monotone (prof F η) := by
  intro a b hab
  simp only [prof]
  refine MeasureTheory.integral_mono ?_ ?_ ?_
  · refine ((hFc.comp (continuous_const.sub continuous_id)).mul hηcont).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.mul_left (f := fun t : ℝ => F (a - t)) hηc
  · refine ((hFc.comp (continuous_const.sub continuous_id)).mul hηcont).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.mul_left (f := fun t : ℝ => F (b - t)) hηc
  · intro t
    exact mul_le_mul_of_nonneg_right (hF (by linarith)) (hη t)

end Work.Profiles
