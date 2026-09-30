import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.SpecialFunctions.Trigonometric

theorem cosh_add_abs_sinh (y : ℝ) : Real.cosh y + |Real.sinh y| = Real.exp |y| := by
  rw [Real.abs_sinh, ← Real.cosh_abs]
  exact Real.cosh_add_sinh |y|

end Commons.Analysis.SpecialFunctions.Trigonometric