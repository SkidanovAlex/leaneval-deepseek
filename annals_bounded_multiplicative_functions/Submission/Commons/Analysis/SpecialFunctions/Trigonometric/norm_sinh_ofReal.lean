import Mathlib.Analysis.Complex.Trigonometric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.SpecialFunctions.Trigonometric

theorem norm_sinh_ofReal (y : ℝ) : ‖Complex.sinh (y : ℂ)‖ = |Real.sinh y| := by
  rw [← Complex.ofReal_sinh]
  rw [Complex.norm_real]
  exact Real.norm_eq_abs _

end Commons.Analysis.SpecialFunctions.Trigonometric