import Mathlib
import Submission.Work.Beltrami.Cauchy

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff Convolution
open Work.Beltrami

/-- The Cauchy kernel `w ↦ (w)⁻¹` is locally integrable on `ℂ`: it is dominated by
`‖w‖ ^ (-1)` with `1 < finrank ℝ ℂ = 2`. -/
private theorem locallyIntegrable_inv_complex :
    LocallyIntegrable (fun w : ℂ => w⁻¹) (volume : Measure ℂ) := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := (volume : Measure ℂ))
    (C := 1) (α := 1)
    (le_of_lt (by rw [Complex.finrank_real_complex]; norm_num))
    (by rw [Complex.finrank_real_complex]; norm_num) ?_ measurable_inv.aestronglyMeasurable
  filter_upwards with x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [norm_inv, Real.rpow_neg_one]
    simp

/-- The Cauchy transform of a smooth compactly supported function is smooth. -/
theorem contDiff_cauchyT (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (cauchyT f) := by
  have hconv : ContDiff ℝ ∞
      (f ⋆[ContinuousLinearMap.mul ℝ ℂ, (volume : Measure ℂ)] (fun w : ℂ => w⁻¹)) :=
    hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hf locallyIntegrable_inv_complex
  have heq : cauchyT f
      = fun z => (Real.pi)⁻¹ •
          (f ⋆[ContinuousLinearMap.mul ℝ ℂ, (volume : Measure ℂ)] (fun w : ℂ => w⁻¹)) z := by
    funext z
    rw [cauchyT_apply, MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    have hint : ∫ (ζ : ℂ), (ζ - z)⁻¹ * f ζ ∂(volume : Measure ℂ)
        = - ∫ (t : ℂ), f t * (z - t)⁻¹ ∂(volume : Measure ℂ) := by
      rw [← integral_neg]
      congr 1
      funext ζ
      rw [show (ζ - z)⁻¹ = -((z - ζ)⁻¹) by
            rw [show ζ - z = -(z - ζ) by ring, inv_neg]]
      ring
    rw [hint, neg_smul, smul_neg, neg_neg]
  rw [heq]
  exact hconv.const_smul (Real.pi)⁻¹

end Work.Beltrami
