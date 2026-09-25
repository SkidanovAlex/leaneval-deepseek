import Mathlib

namespace Work.LT

/-- Arithmetic smoothing bound: if `a, b ≥ 0` and `|a - b| ≤ e`, then
`|a² - b²| ≤ 2 e b + e²`. -/
theorem relT_smooth_arith (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : |a - b| ≤ e) :
    |a ^ 2 - b ^ 2| ≤ 2 * e * b + e ^ 2 := by
  have he : 0 ≤ e := le_trans (abs_nonneg (a - b)) h
  have h1 : a ≤ b + e := by
    have := (abs_le.mp h).2
    linarith
  have hab : a + b ≤ 2 * b + e := by linarith
  have hnn : 0 ≤ a + b := by linarith
  have hsq : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [hsq, abs_mul, abs_of_nonneg hnn]
  calc |a - b| * (a + b) ≤ e * (2 * b + e) :=
        mul_le_mul h hab hnn he
    _ = 2 * e * b + e ^ 2 := by ring

end Work.LT
