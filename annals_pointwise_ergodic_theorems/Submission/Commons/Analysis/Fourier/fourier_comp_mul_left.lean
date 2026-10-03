import Submission.Commons.Analysis.Fourier.fourier_scaled_translate

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

theorem fourier_comp_mul_left (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => f (c * x)) ξ
      = ((c : ℂ))⁻¹ * FourierTransform.fourier f (ξ / c) := by
  have h := fourier_comp_inv_smul (V := ℝ) f (a := c⁻¹) (inv_pos.mpr hc) ξ
  rw [Module.finrank_self, pow_one, inv_inv] at h
  have hfuneq : (fun x : ℝ => f (c * x)) = (fun x : ℝ => f (c • x)) := by
    funext x; rw [smul_eq_mul]
  have harg : c⁻¹ • (ξ : ℝ) = ξ / c := by
    rw [smul_eq_mul]; ring
  rw [hfuneq, h, harg]
  rw [Algebra.smul_def, map_inv₀]
  rfl

end Commons.Analysis.Fourier
