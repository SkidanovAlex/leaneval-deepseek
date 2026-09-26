import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

namespace Work.Smooth.JordanSeparation

/-- Multiplication by `I` on the right of `detV` turns the oriented determinant
into the real inner product: `detV u (I * w) = ⟪u, w⟫_ℝ`. -/
theorem detV_I_mul (u w : ℂ) : Work.Smooth.JordanSeparation.detV u (Complex.I * w) = inner ℝ u w := by
  rw [detV_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp
  ring

end Work.Smooth.JordanSeparation
