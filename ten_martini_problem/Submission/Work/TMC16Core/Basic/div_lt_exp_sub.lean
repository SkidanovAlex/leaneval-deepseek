import Mathlib

namespace Work.TMC16Core.Basic

theorem div_lt_exp_sub {a b X Y : ℝ} (hY : Real.exp Y < b) (ha : 0 ≤ a)
    (hX : a ≤ Real.exp X) : a / b < Real.exp (X - Y) := by
  rw [Real.exp_sub]
  have hYpos : 0 < Real.exp Y := Real.exp_pos Y
  rcases ha.lt_or_eq with ha_pos | ha_eq
  · exact lt_of_lt_of_le
      (div_lt_div_of_pos_left ha_pos hYpos hY)
      (div_le_div_of_nonneg_right hX (le_of_lt hYpos))
  · rw [← ha_eq, zero_div]
    exact div_pos (Real.exp_pos X) hYpos

end Work.TMC16Core.Basic
