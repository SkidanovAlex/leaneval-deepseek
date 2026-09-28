import Mathlib

namespace Work.HP

theorem ceil_logb_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ ∧ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ ≤ 2 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hle : Real.logb 2 x ≤ (⌈Real.logb 2 x⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈Real.logb 2 x⌉₊ : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlog_nonneg
  constructor
  · rw [← Real.rpow_natCast 2 ⌈Real.logb 2 x⌉₊]
    rw [← Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hx0]
    exact hle
  · rw [← Real.rpow_natCast 2 ⌈Real.logb 2 x⌉₊]
    refine le_of_lt ?_
    calc (2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) < 2 ^ (Real.logb 2 x + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
      _ = 2 * x := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
            Real.rpow_logb (by norm_num) (by norm_num) hx0, Real.rpow_one]
          ring

end Work.HP
