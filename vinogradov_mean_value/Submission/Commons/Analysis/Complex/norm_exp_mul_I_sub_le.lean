import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Commons.Analysis.Complex

theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have harg : (b : ℂ) * Complex.I + ((a - b : ℝ) : ℂ) * Complex.I = (a : ℂ) * Complex.I := by
    push_cast
    ring
  have key : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
          (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, harg]
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rw [mul_comm, Real.norm_eq_abs] at h
  exact h

end Commons.Analysis.Complex