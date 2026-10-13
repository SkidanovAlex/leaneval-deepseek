import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

lemma rpow_mul_div_rpow_eq {β x y : ℝ} (hx : 0 < x) (hyx : y ≤ x) :
    x ^ (3 * β) * ((x - y) / x) ^ β = x ^ (2 * β) * (x - y) ^ β := by
  by_cases hβ : β = 0
  · subst hβ; norm_num
  by_cases hxy : x - y = 0
  · rw [hxy]
    simp only [zero_div]
    rw [Real.zero_rpow hβ]
    ring
  · have hpos : 0 < x - y := lt_of_le_of_ne (sub_nonneg.mpr hyx) (Ne.symm hxy)
    rw [Real.div_rpow hpos.le hx.le β]
    have h3 : x ^ (3 * β) = x ^ (2 * β) * x ^ β := by
      rw [show 3 * β = 2 * β + β by ring, Real.rpow_add hx]
    rw [h3]
    have hxβ : x ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx β)
    field_simp

end Work.ConstructionInstance
