import Mathlib

namespace Work.L62

/-- For `0 ≤ t ≤ 1/2`, `exp (-(2t)) ≤ 1 - t`. -/
theorem exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  -- From `exp y ≥ 1 + y` at `y = 2t`:  `exp (2t) ≥ 1 + 2t > 0`.
  have h1 : 1 + 2 * t ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t); linarith
  have hpos : 0 < 1 + 2 * t := by linarith
  -- Taking inverses:  `exp (-(2t)) = 1 / exp (2t) ≤ 1 / (1 + 2t)`.
  have h2 : Real.exp (-(2 * t)) ≤ 1 / (1 + 2 * t) := by
    rw [Real.exp_neg]
    simpa using one_div_le_one_div_of_le hpos h1
  -- And `1 / (1 + 2t) ≤ 1 - t` since `1 ≤ (1 - t)(1 + 2t)`, i.e. `t (1 - 2t) ≥ 0`.
  have h3 : 1 / (1 + 2 * t) ≤ 1 - t := by
    rw [div_le_iff₀ hpos]
    nlinarith [ht, ht0]
  linarith [h2, h3]

end Work.L62
