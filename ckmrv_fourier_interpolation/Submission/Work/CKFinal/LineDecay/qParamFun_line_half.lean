import Mathlib
import Submission.Work.Kernels.Kernels

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-! ## The nome `q(τ) = e^{2π i τ}` on the vertical lines `Re τ = ±1/2`

Write `τ = x + i y` with `q(τ) = e^{2π i x} e^{-2π y}`.  On the two lines `x = ±1/2`
one has `e^{2π i x} = e^{± π i} = -1`, so `q(τ) = -e^{-2π y}` is a negative real number.
The lemma below records this identity exactly in the form in which the line-decay
computation of CKMRV §5 uses it: the nome on either line equals the negative of the
real number `e^{-2π Im τ}`. -/

/-- On `Re τ = ±1/2` the nome `q(τ) = e^{2πiτ}` equals the negative real number
`-e^{-2π Im τ}`. -/
theorem qParamFun_line_half (τ : UpperHalfPlane)
    (hτ : τ.re = 1 / 2 ∨ τ.re = -1 / 2) :
    Work.Kernels.qParamFun τ = -(Real.exp (-(2 * Real.pi * τ.im)) : ℂ) := by
  -- `τ = Re τ + i Im τ` as a complex number.
  have hcoe : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  -- The exponent splits into a real part and a purely imaginary real multiple of `I`.
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = ((-(2 * Real.pi * τ.im) : ℝ) : ℂ) + ((2 * τ.re * Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [hcoe]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  -- `cos (2 x π) = -1` on either line `x = ±1/2`.
  have hcos : Real.cos (2 * τ.re * Real.pi) = -1 := by
    rcases hτ with h | h
    · have : (2 * τ.re * Real.pi : ℝ) = Real.pi := by rw [h]; ring
      rw [this, Real.cos_pi]
    · have : (2 * τ.re * Real.pi : ℝ) = -Real.pi := by rw [h]; ring
      rw [this, Real.cos_neg, Real.cos_pi]
  -- `sin (2 x π) = 0` on either line.
  have hsin : Real.sin (2 * τ.re * Real.pi) = 0 := by
    rcases hτ with h | h
    · have : (2 * τ.re * Real.pi : ℝ) = Real.pi := by rw [h]; ring
      rw [this, Real.sin_pi]
    · have : (2 * τ.re * Real.pi : ℝ) = -Real.pi := by rw [h]; ring
      rw [this, Real.sin_neg, Real.sin_pi, neg_zero]
  rw [Work.Kernels.qParamFun, harg, Complex.exp_add, ← Complex.ofReal_exp,
      Complex.exp_ofReal_mul_I (2 * τ.re * Real.pi), hcos, hsin]
  norm_num

end Work.CKFinal.LineDecay
