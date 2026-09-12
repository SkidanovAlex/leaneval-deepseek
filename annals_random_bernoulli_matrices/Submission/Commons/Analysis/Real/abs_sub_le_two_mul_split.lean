import Mathlib

set_option linter.unusedVariables false

namespace Commons.Analysis.Real

theorem abs_sub_le_two_mul_split {x l r : ℝ} (hr : 0 ≤ r) (h : |x - l| ≤ 2 * r) :
    |x - (l - r)| ≤ r ∨ |x - (l + r)| ≤ r := by
  have hxl_le : x - l ≤ 2 * r := (abs_sub_le_iff.mp h).1
  have hlx_le : l - x ≤ 2 * r := (abs_sub_le_iff.mp h).2
  rcases le_total x l with hxl | hlx
  · left
    apply abs_le.mpr
    constructor
    · nlinarith [hlx_le]
    · nlinarith [hxl]
  · right
    apply abs_le.mpr
    constructor
    · nlinarith [hlx]
    · nlinarith [hxl_le]

end Commons.Analysis.Real
