import Mathlib

namespace Work.TMComp.RedProj

open MeasureTheory AddCircle

theorem fourierCoeffOn_eq_exp_integral (φ : ℝ → ℂ) (k : ℤ) :
    fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k =
      ∫ x in (0:ℝ)..1, φ x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))) := by
  rw [fourierCoeffOn_eq_integral φ k (show (0:ℝ) < 1 by norm_num)]
  simp only [sub_zero, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [smul_eq_mul, fourier_coe_apply]
  simp only [sub_zero, Complex.ofReal_one, div_one]
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-k) * ↑x) =
      Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k * ↑x)) := by
    congr 1; push_cast; ring
  rw [h]
  ring

end Work.TMComp.RedProj
