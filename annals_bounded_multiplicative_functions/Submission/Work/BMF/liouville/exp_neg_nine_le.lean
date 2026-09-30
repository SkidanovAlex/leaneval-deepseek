import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Numerical bound: `exp (-9) ≤ 1/7000`.
Proved by sandwiching `exp (-1)` between `exp_neg_one_lt_d9` and positivity,
raising to the ninth power, and reducing to rational arithmetic. -/
theorem exp_neg_nine_le : Real.exp (-9) ≤ 1/7000 := by
  have h1 : Real.exp (-1) < (0.3678794412 : ℝ) := Real.exp_neg_one_lt_d9
  have h2 : Real.exp (-1) ^ 9 < (0.3678794412 : ℝ) ^ 9 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos _).le (by norm_num)
  have h3 : (0.3678794412 : ℝ) ^ 9 ≤ 1/7000 := by norm_num
  have h4 : Real.exp (-1) ^ 9 = Real.exp (-9) := by
    rw [← Real.exp_nat_mul (-1) 9]
    norm_num
  rw [← h4]
  linarith

end Work.BMF.liouville
