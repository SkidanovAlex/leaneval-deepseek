import Mathlib

namespace Work.FatouL1

set_option linter.unusedSimpArgs false in
theorem normSqSinComplex (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im]
  ring_nf
  rw [Real.cosh_sq]
  nlinarith [Real.sin_sq_add_cos_sq z.re]

end Work.FatouL1
