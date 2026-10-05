import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPB.B1

open MeasureTheory

/-! ## Auxiliary computation

`Complex.exp (-(θ:ℂ) * I) = cos θ - sin θ * I`, and consequently the real and imaginary
parts of `C * exp (-(θ:ℂ) * I)` are trig polynomials in `θ`.

Writing `C = C.re + C.im * I` one obtains
* `Im (C * e^{-iθ}) = C.im * cos θ - C.re * sin θ`,
* `Re (D * e^{-iθ}) = D.re * cos θ + D.im * sin θ`.
-/

private lemma exp_neg_mul_I_eq (θ : ℝ) :
    Complex.exp (-(θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private lemma im_mul_exp_neg_mul_I (C : ℂ) (θ : ℝ) :
    (C * Complex.exp (-(θ : ℂ) * Complex.I)).im = C.im * Real.cos θ - C.re * Real.sin θ := by
  rw [exp_neg_mul_I_eq]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma re_mul_exp_neg_mul_I (D : ℂ) (θ : ℝ) :
    (D * Complex.exp (-(θ : ℂ) * Complex.I)).re = D.re * Real.cos θ + D.im * Real.sin θ := by
  rw [exp_neg_mul_I_eq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The integral over one period of a quadratic trigonometric polynomial
`a cos²θ + b sinθ cosθ + c sin²θ`. -/
private lemma integral_trig (a b c : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (a * Real.cos θ ^ 2 + b * (Real.sin θ * Real.cos θ) + c * Real.sin θ ^ 2) =
      Real.pi * (a + c) := by
  have h1 : IntervalIntegrable (fun θ : ℝ => a * Real.cos θ ^ 2) volume (0 : ℝ) (2 * Real.pi) := by
    apply Continuous.intervalIntegrable; fun_prop
  have h2 : IntervalIntegrable (fun θ : ℝ => b * (Real.sin θ * Real.cos θ)) volume (0 : ℝ)
      (2 * Real.pi) := by
    apply Continuous.intervalIntegrable; fun_prop
  have h3 : IntervalIntegrable (fun θ : ℝ => c * Real.sin θ ^ 2) volume (0 : ℝ) (2 * Real.pi) := by
    apply Continuous.intervalIntegrable; fun_prop
  have h12 : IntervalIntegrable
      (fun θ : ℝ => a * Real.cos θ ^ 2 + b * (Real.sin θ * Real.cos θ)) volume (0 : ℝ)
      (2 * Real.pi) := h1.add h2
  rw [intervalIntegral.integral_add h12 h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cos_sq, integral_sin_mul_cos₁, integral_sin_sq]
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
  ring

theorem thetaIntegral (C D : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (C * Complex.exp (-(θ : ℂ) * Complex.I)).im *
          (D * Complex.exp (-(θ : ℂ) * Complex.I)).re
      = Real.pi * Work.RPV.ωC D C := by
  have hkey : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (C * Complex.exp (-(θ : ℂ) * Complex.I)).im *
          (D * Complex.exp (-(θ : ℂ) * Complex.I)).re)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((C.im * D.re) * Real.cos θ ^ 2 +
          (C.im * D.im - C.re * D.re) * (Real.sin θ * Real.cos θ) +
          (-(C.re * D.im)) * Real.sin θ ^ 2) :=
    intervalIntegral.integral_congr
      (fun θ _ => by rw [im_mul_exp_neg_mul_I, re_mul_exp_neg_mul_I]; ring)
  rw [hkey, integral_trig]
  congr 1
  simp only [Work.RPV.ωC, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

end Work.RPB.B1
