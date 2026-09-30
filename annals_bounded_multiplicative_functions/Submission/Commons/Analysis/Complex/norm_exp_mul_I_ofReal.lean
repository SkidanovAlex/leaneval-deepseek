import Mathlib.Analysis.Complex.Trigonometric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Complex

theorem norm_exp_mul_I_ofReal (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  simp

end Commons.Analysis.Complex