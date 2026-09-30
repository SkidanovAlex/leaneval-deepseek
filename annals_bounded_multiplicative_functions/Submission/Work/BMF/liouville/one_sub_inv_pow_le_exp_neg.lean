import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- For a natural number `n ≥ 2` and any exponent `m`, the inequality `(1 - 1/n)^m ≤ exp(-m/n)`.
This is the standard estimate `(1 + x)^m ≤ e^{xm}` applied with `x = -1/n`, which holds because
`1 - 1/n ≥ 0` (from `n ≥ 2`) and the elementary bound `1 - y ≤ e^{-y}`. -/
theorem one_sub_inv_pow_le_exp_neg (n m : ℕ) (hn : 2 ≤ n) : (1 - 1 / (n : ℝ)) ^ m ≤ Real.exp (-((m : ℝ) / (n : ℝ))) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- `1 - 1/n` is nonnegative, so powers behave monotonically.
  have hx : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hpos]
    linarith
  -- The elementary bound `1 - y ≤ e^{-y}` with `y = 1/n`.
  have h1 : 1 - 1 / (n : ℝ) ≤ Real.exp (-(1 / (n : ℝ))) := Real.one_sub_le_exp_neg _
  have h2 : (1 - 1 / (n : ℝ)) ^ m ≤ (Real.exp (-(1 / (n : ℝ)))) ^ m :=
    pow_le_pow_left₀ hx h1 m
  -- Rewrite the right-hand power as a single exponential.
  have h3 : (Real.exp (-(1 / (n : ℝ)))) ^ m = Real.exp (-((m : ℝ) / (n : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  linarith [h2, h3]

end Work.BMF.liouville
