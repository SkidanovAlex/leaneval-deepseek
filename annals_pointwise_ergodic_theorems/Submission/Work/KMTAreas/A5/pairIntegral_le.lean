import Mathlib
import Submission.Work.KMTAreas.A5.interpDefs
import Submission.Port.Aesm

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-!
# Pairing with a contractive test function does not increase the `ℓ¹` norm

For a function `F : ℤ → ℂ` and a test function `φ` with `‖φ x‖ ≤ 1` everywhere, the pairing
`∫ x, F x * φ x ∂count` is bounded in `ℝ≥0∞`-valued norm by the `ℒ¹` seminorm of `F`.  This is the
elementary duality estimate `(ℓ¹)' = ℓ^∞` used in the interpolation step of §5: the operator norm
of `T` in `ℒ¹` controls the pairing of `T u v` against any `ℓ^∞` test function.

The result is stated in `ℝ≥0∞`, so it holds unconditionally (including the case where the pairing
integral is a non-integrable junk value, where `‖∫ ⋯‖ₑ = 0`).
-/

/-- The `ℝ≥0∞`-valued norm of the pairing of `F` against a test function with `‖φ x‖ ≤ 1` is
bounded by the `ℒ¹` seminorm of `F`. -/
theorem enorm_pairing_le_eLpNorm_one {F φ : ℤ → ℂ} (hφ : ∀ x : ℤ, ‖φ x‖ ≤ 1) :
    ‖∫ x, F x * φ x ∂MeasureTheory.Measure.count‖ₑ
      ≤ MeasureTheory.eLpNorm F 1 MeasureTheory.Measure.count := by
  have h1 : (∫⁻ x, ‖F x * φ x‖ₑ ∂MeasureTheory.Measure.count)
      ≤ ∫⁻ x, ‖F x‖ₑ ∂MeasureTheory.Measure.count := by
    refine lintegral_mono fun x => ?_
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hφ x)
  exact (enorm_integral_le_lintegral_enorm (fun x => F x * φ x)).trans
    (h1.trans (le_of_eq (eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)).symm))

/-- **The pairing estimate of §5.**  If a bilinear operator `T` is bounded from `ℓ^p × ℓ^q` to
`ℓ¹` with constant `M`, then the pairing of `T u v` against any test function `φ` with
`‖φ x‖ ≤ 1` is bounded by `M ‖u‖_p ‖v‖_q`.  No boundedness of `u`, `v` is needed beyond what the
hypothesis already provides: the conclusion is stated in `ℝ≥0∞`. -/
theorem pairIntegral_le (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)) {p q : ℝ} {M : NNReal}
    (h : ∀ u v : ℤ → ℂ, MeasureTheory.eLpNorm (T u v) 1 MeasureTheory.Measure.count
      ≤ (M : ENNReal) * MeasureTheory.eLpNorm u (ENNReal.ofReal p) MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm v (ENNReal.ofReal q) MeasureTheory.Measure.count)
    {φ : ℤ → ℂ} (hφ : ∀ x : ℤ, ‖φ x‖ ≤ 1)
    {u v : ℤ → ℂ} (hu : Work.KMTAreas.A5.BoundedZ u) (hv : Work.KMTAreas.A5.BoundedZ v) :
    ‖∫ x, T u v x * φ x ∂MeasureTheory.Measure.count‖ₑ
      ≤ (M : ENNReal) * MeasureTheory.eLpNorm u (ENNReal.ofReal p) MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm v (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  exact (enorm_pairing_le_eLpNorm_one hφ).trans (h u v)

end Work.KMTAreas.A5
