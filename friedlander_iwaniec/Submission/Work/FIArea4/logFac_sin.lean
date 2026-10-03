import Mathlib
import Submission.Work.FITop3.Defs3

namespace Work.FIArea4

open Complex

/-- `Im(z̄₁ z₂) = |z₁||z₂| sin(arg z₂ - arg z₁)`: the imaginary part of `z̄₁z₂` is the
cross product of the two vectors, i.e. the product of the moduli times the sine of the
angle between them. -/
lemma im_star_mul (z1 z2 : GaussianInt) :
    ((star z1 * z2 : GaussianInt) : ℂ).im
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖
        * Real.sin (Complex.arg (z2 : ℂ) - Complex.arg (z1 : ℂ)) := by
  have h1 := Complex.norm_mul_cos_arg (z1 : ℂ)
  have h2 := Complex.norm_mul_sin_arg (z1 : ℂ)
  have h3 := Complex.norm_mul_cos_arg (z2 : ℂ)
  have h4 := Complex.norm_mul_sin_arg (z2 : ℂ)
  rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Real.sin_sub, ← h1, ← h4, ← h3, ← h2]
  ring

/-- `|z₁z₂|² = (|z₁||z₂|)²` for Gaussian integers, expressed through `gnorm` and the complex
moduli. -/
lemma sq_gnorm_mul (z1 z2 : GaussianInt) :
    ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) = (‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖) ^ 2 := by
  have h1 : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = Complex.normSq ((z1 * z2 : GaussianInt) : ℂ) := by
    rw [Work.FIPlan.gnorm, GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm]
  rw [h1, GaussianInt.toComplex_mul, Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  ring

/-- `|Δ(z₁,z₂)| = |Im(z̄₁z₂)|`: `absDelta` as a real number is the absolute value of the
complex number `z̄₁z₂`. -/
lemma absDelta_cast (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((star z1 * z2 : GaussianInt) : ℂ).im| := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.Delta]
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, GaussianInt.intCast_im]

theorem logFac_sin (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    Work.FITop3.logFac z1 z2
      = -Real.log (|Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| / 2) := by
  have hRnn : (0 : ℝ) ≤ ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsqrt : Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by
    rw [sq_gnorm_mul, Real.sqrt_sq hRnn]
  have habs : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖
        * |Real.sin (Complex.arg (z2 : ℂ) - Complex.arg (z1 : ℂ))| := by
    rw [absDelta_cast, im_star_mul, abs_mul, abs_of_nonneg hRnn]
  have hne : ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖
      * |Real.sin (Complex.arg (z2 : ℂ) - Complex.arg (z1 : ℂ))| ≠ 0 := by
    intro h
    apply hΔ
    have : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) = 0 := by rw [habs, h]
    exact_mod_cast this
  have hsne : |Real.sin (Complex.arg (z2 : ℂ) - Complex.arg (z1 : ℂ))| ≠ 0 :=
    (mul_ne_zero_iff.mp hne).2
  have harg : 2 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = (|Real.sin (Complex.arg (z2 : ℂ) - Complex.arg (z1 : ℂ))| / 2)⁻¹ := by
    rw [hsqrt, habs, inv_div, div_eq_div_iff hne hsne]
    ring
  rw [Work.FITop3.logFac, harg, Real.log_inv]

end Work.FIArea4
