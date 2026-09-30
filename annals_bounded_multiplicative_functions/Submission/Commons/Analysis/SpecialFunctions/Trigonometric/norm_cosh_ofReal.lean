import Mathlib.Analysis.Complex.Trigonometric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.SpecialFunctions.Trigonometric

theorem norm_cosh_ofReal (y : ℝ) : ‖Complex.cosh (y : ℂ)‖ = Real.cosh y := by
  rw [← Complex.ofReal_cosh y]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.cosh_pos y)]

end Commons.Analysis.SpecialFunctions.Trigonometric