import Mathlib

namespace Work.LinnikContract.API

/-- Decomposition of the complex hyperbolic sine along real and imaginary parts:
`sinh z = sinh(Re z) cos(Im z) + cosh(Re z) sin(Im z) · i`. -/
private lemma sinh_re_add_im (z : ℂ) :
    Complex.sinh z =
      ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ) +
        ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  ring

/-- The squared modulus of the complex hyperbolic sine in terms of its real and imaginary parts:
`‖sinh z‖² = sinh(Re z)² + sin(Im z)²`.  This is the standard identity
`sinh(u+iv) = sinh u cos v + i cosh u sin v`, combined with `cosh² − sinh² = 1`. -/
theorem norm_sinh_sq (z : ℂ) :
    ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, sinh_re_add_im, Complex.normSq_add_mul_I]
  nlinarith [Real.cosh_sq_sub_sinh_sq z.re, Real.cos_sq_add_sin_sq z.im]

end Work.LinnikContract.API
