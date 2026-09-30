import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- `π ^ 2 / 2 ≤ 5`, equivalently `π ≤ √10`.  Since `π < 3.15` (Mathlib's `Real.pi_lt_d2`)
and `3.15 ^ 2 = 9.9225 < 10`, this is immediate. -/
theorem pi_sq_le_ten : Real.pi ^ 2 / 2 ≤ 5 := by
  have h := Real.pi_lt_d2
  have hpos := Real.pi_pos
  nlinarith [sq_nonneg (Real.pi - 3.15), sq_nonneg (Real.pi + 3.15)]

end Work.BMF
