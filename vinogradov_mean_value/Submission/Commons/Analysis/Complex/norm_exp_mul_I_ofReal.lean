import Mathlib.Analysis.Complex.Trigonometric

namespace Commons.Analysis.Complex

theorem norm_exp_mul_I_ofReal (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  simp

end Commons.Analysis.Complex