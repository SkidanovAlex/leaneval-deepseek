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

/-- The affine part `A + B * (r - t)` inherits integrability from `η` against which it is
integrated, and its weighted integral picks out the moments of `η`. -/
theorem integral_affine_mul {η : ℝ → ℝ} (A B r : ℝ) (hηcont : Continuous η)
    (hηc : HasCompactSupport η) (hη1 : ∫ t, η t = 1) (hηid : ∫ t, t * η t = 0) :
    ∫ t, (A + B * (r - t)) * η t = A + B * r := by
  have hηint : Integrable η := hηcont.integrable_of_hasCompactSupport hηc
  have htηint : Integrable (fun t : ℝ => t * η t) :=
    (continuous_id.mul hηcont).integrable_of_hasCompactSupport
      (hηc.mul_left (f := fun t : ℝ => t))
  have hcongr : (fun t : ℝ => (A + B * (r - t)) * η t)
      = fun t : ℝ => (A + B * r) * η t - B * (t * η t) := by
    funext t; ring
  rw [hcongr]
  rw [integral_sub (hηint.const_mul _) (htηint.const_mul _)]
  rw [integral_const_mul, integral_const_mul, hη1, hηid]
  ring

/-- The smoothing `prof F η` of a function `F` dominating an affine function `A + B * t`
dominates the same affine function, when `η` is a nonnegative probability density with
vanishing first moment (`∫ t * η t = 0`), i.e. `η` is centred at `0`. -/
theorem prof_ge_affine {F η : ℝ → ℝ} (A B : ℝ) (hF : ∀ t, A + B * t ≤ F t) (hFc : Continuous F)
    (hη : ∀ t, 0 ≤ η t) (hηcont : Continuous η) (hηc : HasCompactSupport η)
    (hη1 : ∫ t, η t = 1) (hηid : ∫ t, t * η t = 0) :
    ∀ r, A + B * r ≤ prof F η r := by
  intro r
  have hFcont : Continuous fun t : ℝ => F (r - t) :=
    hFc.comp (continuous_const.sub continuous_id)
  have hFsupp : HasCompactSupport fun t : ℝ => F (r - t) * η t :=
    hηc.mul_left (f := fun t : ℝ => F (r - t))
  have hFint : Integrable (fun t : ℝ => F (r - t) * η t) :=
    (hFcont.mul hηcont).integrable_of_hasCompactSupport hFsupp
  have hηint : Integrable η := hηcont.integrable_of_hasCompactSupport hηc
  have htηint : Integrable (fun t : ℝ => t * η t) :=
    (continuous_id.mul hηcont).integrable_of_hasCompactSupport
      (hηc.mul_left (f := fun t : ℝ => t))
  have hgint : Integrable (fun t : ℝ => (A + B * (r - t)) * η t) := by
    have hcongr : (fun t : ℝ => (A + B * (r - t)) * η t)
        = fun t : ℝ => (A + B * r) * η t - B * (t * η t) := by
      funext t; ring
    rw [hcongr]
    exact (hηint.const_mul _).sub (htηint.const_mul _)
  have hpoint : ∀ t, (A + B * (r - t)) * η t ≤ F (r - t) * η t :=
    fun t => mul_le_mul_of_nonneg_right (hF (r - t)) (hη t)
  have hmain : ∫ t, (A + B * (r - t)) * η t ≤ ∫ t, F (r - t) * η t :=
    integral_mono hgint hFint hpoint
  calc A + B * r = ∫ t, (A + B * (r - t)) * η t :=
        (integral_affine_mul A B r hηcont hηc hη1 hηid).symm
    _ ≤ ∫ t, F (r - t) * η t := hmain
    _ = prof F η r := rfl

end Work.Profiles
