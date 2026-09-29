import Mathlib

namespace Work.APsi

/-- If `z` is a complex root of `A z² - D z + A = -s` with `A > 0`,
`D² < 4A²` and `s ≥ 0`, then `z` is non-real and `‖z‖² = 1 + s/A`.

Indeed `z` and `z̄` are the two roots of the real quadratic
`A X² - D X + (A+s)`, whose discriminant `D² - 4A(A+s) < 0` is strictly negative. -/
theorem quad_neg_real {A D s : ℝ} (hA : 0 < A) (hD : D ^ 2 < 4 * A ^ 2) {z : ℂ}
    (h : (A : ℂ) * z ^ 2 - (D : ℂ) * z + (A : ℂ) = -(s : ℂ)) (hs : 0 ≤ s) :
    ‖z‖ ^ 2 = 1 + s / A := by
  -- real and imaginary parts of the defining equation
  have hre : A * (z.re ^ 2 - z.im ^ 2) - D * z.re + A + s = 0 := by
    have h1 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, pow_two] at h1
    linarith
  have him : z.im * (2 * A * z.re - D) = 0 := by
    have h1 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_im, pow_two] at h1
    linarith
  -- the modulus squared
  have hkey : z.re ^ 2 + z.im ^ 2 = (A + s) / A := by
    rcases mul_eq_zero.mp him with hy | hx
    · -- `z` is real: impossible, the discriminant is strictly negative
      rw [hy] at hre
      nlinarith [sq_nonneg (2 * A * z.re - D), sq_nonneg A]
    · -- `2 A Re z = D`, substitute into the real part
      have hDsub : D = 2 * A * z.re := by linarith
      rw [hDsub] at hre
      have hmain : A * (z.re ^ 2 + z.im ^ 2) = A + s := by nlinarith
      rw [eq_div_iff (ne_of_gt hA)]
      linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hfin : z.re * z.re + z.im * z.im = (A + s) / A := by
    rw [← hkey]; ring
  rw [hfin]
  field_simp

end Work.APsi
