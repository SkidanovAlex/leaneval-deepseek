import Mathlib

namespace Work.HP.NA

/-- For `p ≥ 1`, the map `x ↦ 1 / p ^ x` is antitone on `ℝ` when the exponent is
compared against a natural number: for `c ≤ m`, `1 / p ^ m ≤ 1 / p ^ c`. -/
theorem one_div_pow_le_one_div_rpow (p : ℝ) (hp : 1 ≤ p) (m : ℕ) (c : ℝ) (hc : c ≤ (m : ℝ)) :
    1 / p ^ m ≤ 1 / p ^ c := by
  rw [← Real.rpow_natCast p m]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hp) c)
    (Real.rpow_le_rpow_of_exponent_le hp hc)

end Work.HP.NA
