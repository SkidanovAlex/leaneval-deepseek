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

open MeasureTheory Filter

/-- If the model function `F` is constantly `c` on `(-∞, 3/4]`, then smoothing it against
any nonnegative bump `η` supported in `[-1/4, 1/4]` of total mass `1` gives back `c` on
`(-∞, 1/2]`: for `r ≤ 1/2` and `|t| < 1/4` one has `r - t ≤ 3/4`, and for `|t| ≥ 1/4`
both sides of the pointwise identity vanish because `η t = 0`. -/
theorem prof_core_const {F η : ℝ → ℝ} (c : ℝ) (hF : ∀ t ≤ 3/4, F t = c) (hFc : Continuous F)
    (hη : ∀ t, 0 ≤ η t) (hηcont : Continuous η) (hηc : HasCompactSupport η)
    (hηsupp : ∀ t, 1/4 ≤ |t| → η t = 0) (hη1 : ∫ t, η t = 1) :
    ∀ r ≤ 1/2, prof F η r = c := by
  intro r hr
  have hpoint : ∀ t, F (r - t) * η t = c * η t := by
    intro t
    rcases eq_or_ne (η t) 0 with h | h
    · simp [h]
    · have hlt : |t| < 1/4 := by
        by_contra hcon
        rw [not_lt] at hcon
        exact h (hηsupp t hcon)
      have hrt : r - t ≤ 3/4 := by
        rw [abs_lt] at hlt
        linarith [hlt.1, hlt.2]
      rw [hF (r - t) hrt]
  rw [prof]
  calc ∫ t, F (r - t) * η t
      = ∫ t, c * η t := integral_congr_ae (Eventually.of_forall hpoint)
    _ = c * ∫ t, η t := integral_const_mul c η
    _ = c := by rw [hη1, mul_one]

end Work.Profiles
