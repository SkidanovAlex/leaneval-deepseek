import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- For `2 ≤ A ≤ B`, `log (log B / log A) ≤ log (B / A) / log A`: with `u = log B / log A ≥ 1`
this reads `log u ≤ u - 1`. -/
theorem loglog_div_le (A B : ℝ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    Real.log (Real.log B / Real.log A) ≤ Real.log (B / A) / Real.log A := by
  have hA1 : (1:ℝ) < A := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  have hlogB : Real.log A ≤ Real.log B := Real.log_le_log hApos hAB
  have hlogBpos : 0 < Real.log B := lt_of_lt_of_le hlogA hlogB
  have hlogu : Real.log (Real.log B / Real.log A) ≤ Real.log B / Real.log A - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hlogBpos hlogA)
  have hdiv : Real.log (B / A) / Real.log A = Real.log B / Real.log A - 1 := by
    rw [Real.log_div (ne_of_gt hBpos) (ne_of_gt hApos), sub_div, div_self (ne_of_gt hlogA)]
  rw [hdiv]
  exact hlogu

end Work.BMF.mr_direct
