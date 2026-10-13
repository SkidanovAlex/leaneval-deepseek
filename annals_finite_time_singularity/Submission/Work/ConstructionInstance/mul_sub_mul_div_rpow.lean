import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

lemma mul_sub_mul_div_rpow {β x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    x ^ (3 * β) * (1 - (1 - (x - y) / x) ^ (3 * β)) = x ^ (3 * β) - y ^ (3 * β) := by
  have h1 : 1 - (x - y) / x = y / x := by
    field_simp
    ring
  rw [h1, Real.div_rpow hy hx.le, mul_sub, mul_one,
    mul_div_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hx _))]

end Work.ConstructionInstance
