import Mathlib
import Submission.Work.FatouL1.solverKernel

namespace Work.FatouL1

/-- The cotangent at the point `π (-1/2 + i y)` equals `-i tanh (π y)`.
This is the standard identification of the boundary lines of the Fatou
coordinate strip with the real axis under the (co)tangent map. -/
theorem cotPiNegHalf (y : ℝ) :
    Complex.cot (Real.pi * ((-1 / 2 : ℂ) + (y : ℂ) * Complex.I)) =
      -Complex.I * (Real.tanh (Real.pi * y) : ℂ) := by
  -- Write the argument as `-π/2 + (π y) i` and split real and imaginary parts.
  have hz : Real.pi * ((-1 / 2 : ℂ) + (y : ℂ) * Complex.I) =
      -((Real.pi : ℂ) / 2) + ((Real.pi : ℂ) * (y : ℂ)) * Complex.I := by
    ring
  rw [hz, Complex.cot_eq_cos_div_sin, Complex.cos_add_mul_I, Complex.sin_add_mul_I]
  -- `cos (-π/2) = 0` and `sin (-π/2) = -1`.
  rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  -- Push the real `cosh`/`sinh` through the coercion and unfold `tanh`.
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    Complex.ofReal_tanh]
  rw [Complex.tanh_eq_sinh_div_cosh, ← Complex.ofReal_sinh (Real.pi * y),
    ← Complex.ofReal_cosh (Real.pi * y)]
  ring_nf

end Work.FatouL1
