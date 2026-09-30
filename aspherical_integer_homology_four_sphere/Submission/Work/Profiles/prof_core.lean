import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ContDiff

open MeasureTheory Filter

namespace Work.Profiles

theorem prof_core {F η : ℝ → ℝ} (hF : ∀ t ≤ 3/4, F t = t) (hFc : Continuous F)
    (hη : ∀ t, 0 ≤ η t) (hηcont : Continuous η) (hηc : HasCompactSupport η)
    (hηsupp : ∀ t, 1/4 ≤ |t| → η t = 0) (hη1 : ∫ t, η t = 1) (hηid : ∫ t, t * η t = 0) :
    ∀ r ≤ 1/2, prof F η r = r := by
  intro r hr
  have hηint : Integrable η volume := hηcont.integrable_of_hasCompactSupport hηc
  have hpoint : ∀ t, F (r - t) * η t = (r - t) * η t := by
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
  have hint1 : Integrable (fun t : ℝ => r * η t) volume := hηint.const_mul r
  have hint2 : Integrable (fun t : ℝ => t * η t) volume :=
    (continuous_id.mul hηcont).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hηc)
  rw [prof]
  calc ∫ t, F (r - t) * η t
      = ∫ t, (r - t) * η t := integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∫ t, (r * η t - t * η t) := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          ring
    _ = (∫ t, r * η t) - (∫ t, t * η t) := integral_sub hint1 hint2
    _ = r * (∫ t, η t) - (∫ t, t * η t) := by rw [integral_const_mul]
    _ = r := by rw [hη1, hηid]; ring

end Work.Profiles
