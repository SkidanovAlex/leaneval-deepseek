import Mathlib
import Submission.Work.HP.ceil_logb_bounds

namespace Work.HP.MDEstimates

/-- For every real `x ≥ 1`, writing `n = ⌈logb 2 x⌉₊` for the ceiling of the binary
logarithm of `x`, we have `2 ^ (2 * n) ≤ 4 * x ^ 2`.

Indeed, `Work.HP.ceil_logb_bounds` gives `2 ^ n ≤ 2 * x`; squaring this (both sides are
nonnegative) yields `(2 ^ n) ^ 2 ≤ (2 * x) ^ 2 = 4 * x ^ 2`, and `(2 ^ n) ^ 2 = 2 ^ (2 * n)`. -/
theorem two_pow_ceillogb_sq_le (x : ℝ) (hx : 1 ≤ x) :
    (2:ℝ) ^ (2 * ⌈Real.logb 2 x⌉₊) ≤ 4 * x ^ 2 := by
  have h2n : (2:ℝ) ^ ⌈Real.logb 2 x⌉₊ ≤ 2 * x := (Work.HP.ceil_logb_bounds hx).2
  have hsq : ((2:ℝ) ^ ⌈Real.logb 2 x⌉₊) ^ 2 ≤ (2 * x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2n 2
  calc (2:ℝ) ^ (2 * ⌈Real.logb 2 x⌉₊)
      = ((2:ℝ) ^ ⌈Real.logb 2 x⌉₊) ^ 2 := by rw [mul_comm 2 ⌈Real.logb 2 x⌉₊, pow_mul]
    _ ≤ (2 * x) ^ 2 := hsq
    _ = 4 * x ^ 2 := by ring

end Work.HP.MDEstimates
