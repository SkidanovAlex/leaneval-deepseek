import Mathlib

open MeasureTheory intervalIntegral
open scoped Real

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- Real part of the Laplace kernel times a real number. -/
theorem re_exp_mul {z : ℂ} {t y : ℝ} :
    (Complex.exp (-(z * (t : ℂ))) * ((y : ℝ) : ℂ)).re
      = Real.exp (-(z.re * t)) * Real.cos (z.im * t) * y := by
  have h1 : -(z * (t : ℂ)) = ((-(z.re * t) : ℝ) : ℂ) + ((-(z.im * t) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.add_re, Complex.ofReal_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.neg_im]
      ring
    · simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        add_zero, Complex.add_im, Complex.ofReal_mul, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.neg_re]
      ring
  rw [h1, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I, Real.cos_neg,
    Real.sin_neg]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.mul_re,
    Complex.add_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul,
    sub_zero, zero_sub, add_zero, neg_zero]

/-- `ℜ F(z) = ∫₀^{x₀} e^{-(Re z)t} cos((Im z)t) f(t) dt` for real-valued `f`. -/
theorem re_laplace_eq {x₀ : ℝ} {z : ℂ} {f : ℝ → ℝ}
    (hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)) volume (0:ℝ) x₀) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..x₀, Real.exp (-(z.re * t)) * Real.cos (z.im * t) * f t := by
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (L := Complex.reCLM) (a := (0:ℝ))
    (b := x₀) (μ := volume) hint
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t _
  exact re_exp_mul

end Commons.NumberTheory.Linnik
