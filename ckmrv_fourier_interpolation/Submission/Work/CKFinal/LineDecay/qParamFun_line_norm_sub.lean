import Mathlib
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Kernels.Kernels

namespace Work.CKFinal.LineDecay

noncomputable section

/-! ## The nome on the two vertical lines `Re τ = ±1/2`

`q(τ) = e^{2π i τ}`.  Writing `τ = x + iy`, `q(τ) = e^{2π i x} e^{-2π y}`, and on the two
lines `x = ±1/2` the first factor is `e^{±π i} = -1`.  Hence on those lines the nome is the
*negative* real number `-e^{-2π y}`, whose modulus is `e^{-2π y} = ‖q(τ)‖`. -/

/-- On `Re τ = ±1/2` the nome equals the negative real number `-e^{-2π Im τ}`. -/
lemma qParamFun_eq_neg_exp (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) :
    Work.Kernels.qParamFun τ = -((Real.exp (-(2 * Real.pi * τ.im)) : ℝ) : ℂ) := by
  have hcoe : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = 2 * (Real.pi : ℂ) * Complex.I * (τ.re : ℂ) + ((-(2 * Real.pi * τ.im) : ℝ) : ℂ) := by
    rw [hcoe]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hx : 2 * τ.re = 1 ∨ 2 * τ.re = -1 := by
    rcases hre with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ.re : ℂ)) = -1 := by
    have harg2 : 2 * (Real.pi : ℂ) * Complex.I * (τ.re : ℂ)
        = ((2 * τ.re : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg2]
    rcases hx with hx | hx
    · rw [hx]; simp [Complex.exp_pi_mul_I]
    · rw [hx]; simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [Work.Kernels.qParamFun, harg, Complex.exp_add, h1, ← Complex.ofReal_exp]
  ring

/-- The nome on the imaginary axis is the positive real number `e^{-2π t}`. -/
lemma qParamFun_imagAxis_eq (t : ℝ) (ht : 0 < t) :
    Work.Kernels.qParamFun (Work.Kernels.imagAxis t ht)
      = ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [Work.Kernels.qParamFun, hcoe]
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I)
      = ((-(2 * Real.pi * t) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [harg, ← Complex.ofReal_exp]

/-- The distance from the nome on one of the two lines `Re τ = ±1/2` to the nome on the
imaginary axis is the sum of the two moduli: `|q(τ) - q(it)| = e^{-2π Im τ} + e^{-2π t}`. -/
theorem qParamFun_line_norm_sub (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (t : ℝ) (ht : 0 < t) :
    ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun (Work.Kernels.imagAxis t ht)‖
      = Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t)) := by
  rw [qParamFun_eq_neg_exp τ hre, qParamFun_imagAxis_eq t ht]
  have hsum : -((Real.exp (-(2 * Real.pi * τ.im)) : ℝ) : ℂ)
      - ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ)
      = -(((Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t)) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hsum, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

end

end Work.CKFinal.LineDecay
