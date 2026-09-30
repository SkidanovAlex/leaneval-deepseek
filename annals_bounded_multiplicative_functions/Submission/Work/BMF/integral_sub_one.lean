import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem integral_sub_one (δ : ℝ) :
    ∫ s in (1:ℝ)..(1+δ), (s - 1) = δ^2/2 := by
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const]
  rw [integral_id, intervalIntegral.integral_const]
  norm_num
  ring

end Work.BMF
