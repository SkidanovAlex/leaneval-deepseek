import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Real

theorem rpow_le_max_one {x θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) : x ^ θ ≤ max 1 x := by
  by_cases hx1 : 1 ≤ x
  · calc x ^ θ ≤ x ^ 1 := Real.rpow_le_rpow_of_exponent_le hx1 hθ1
      _ = x := Real.rpow_one x
      _ ≤ max 1 x := le_max_right _ _
  · calc x ^ θ ≤ 1 := Real.rpow_le_one hx (le_of_lt (not_le.mp hx1)) hθ0
      _ ≤ max 1 x := le_max_left _ _

end Commons.Analysis.Real