import Mathlib

namespace Work.FatouL1

/-- For a complex number `z`, the squared modulus of `cos z` is
`Real.cos z.re ^ 2 + Real.sinh z.im ^ 2`; equivalently
`|cos(x + i y)| ^ 2 = cos(x)^2 + sinh(y)^2`. -/
theorem normSqCosComplex (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, add_zero, zero_sub, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, sub_zero, neg_mul,
    mul_neg]
  ring_nf
  rw [Real.cosh_sq]
  nlinarith [Real.sin_sq_add_cos_sq z.re]

end Work.FatouL1
