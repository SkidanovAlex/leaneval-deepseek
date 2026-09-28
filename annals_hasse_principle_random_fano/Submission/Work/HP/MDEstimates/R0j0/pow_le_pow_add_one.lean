import Mathlib

namespace Work.HP.MDEstimates.R0j0

theorem pow_le_pow_add_one {x : ℝ} (hx : 0 ≤ x) {k n : ℕ} (hkn : k ≤ n) :
    x ^ k ≤ x ^ n + 1 := by
  rcases le_total 1 x with hx1 | hx1
  · have : x ^ k ≤ x ^ n := pow_le_pow_right₀ hx1 hkn
    linarith
  · have hk : x ^ k ≤ 1 := pow_le_one₀ hx hx1
    have hn : 0 ≤ x ^ n := pow_nonneg hx n
    linarith

end Work.HP.MDEstimates.R0j0
