import Mathlib

namespace Work.EQ

theorem lmInvLipschitz {c x y : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| / c^2 := by
  have hx0 : 0 < x := lt_of_lt_of_le hc hx
  have hy0 : 0 < y := lt_of_lt_of_le hc hy
  have hxy : c^2 ≤ x * y := by
    nlinarith [mul_le_mul hx hy (le_of_lt hc) (le_of_lt hx0)]
  rw [inv_sub_inv (ne_of_gt hx0) (ne_of_gt hy0), abs_div, abs_of_pos (mul_pos hx0 hy0),
    abs_sub_comm y x]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hxy

end Work.EQ
