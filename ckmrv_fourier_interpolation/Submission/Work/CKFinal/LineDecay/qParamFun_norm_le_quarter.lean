import Mathlib
import Submission.Work.Kernels.Classical

namespace Work.CKFinal.LineDecay

/-- On the half-plane `Im z ≥ 1` the nome `q = exp (2 π i z)` has modulus
`exp (-2 π Im z) ≤ exp (-2 π) ≤ 1/4`. -/
theorem qParamFun_norm_le_quarter (z : UpperHalfPlane) (hz : 1 ≤ z.im) :
    ‖Work.Kernels.qParamFun z‖ ≤ 1 / 4 := by
  rw [Work.Kernels.qParamFun, Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * (z : ℂ)).re = -(2 * Real.pi * z.im) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_im]
  rw [hre]
  have hmono : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hz]
  refine le_trans hmono ?_
  have hexp4 : (4 : ℝ) ≤ Real.exp 4 := by
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 2]
  have hpi : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hexp : (4 : ℝ) ≤ Real.exp (2 * Real.pi) := le_trans hexp4 (Real.exp_le_exp.mpr hpi)
  rw [Real.exp_neg]
  calc (Real.exp (2 * Real.pi))⁻¹ ≤ (4 : ℝ)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hexp
    _ = 1 / 4 := by norm_num

end Work.CKFinal.LineDecay
