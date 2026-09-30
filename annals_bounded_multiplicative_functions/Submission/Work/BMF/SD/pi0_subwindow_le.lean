import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- `π₀(P) = P / log P` is increasing on `(1, ∞)`: it is the product of the increasing
factors `P/1`... more directly, on `(1, ∞)` the map `P ↦ P / log P` is strictly increasing
since its derivative is `(log P - 1)/log P ^ 2 > 0`.  We only need the elementary
consequence that enlarging the argument by a factor at most `7/5` enlarges `π₀` by at
most that factor, for arguments `≥ 2`.

For `2 ≤ a ≤ a' ≤ 7a/5` we have `log a ≤ log a'` and `log a, log a' > 0`, hence
`a'/log a' ≤ (7a/5)/log a' ≤ (7a/5)/log a = (7/5)·(a/log a)`. -/
theorem pi0_subwindow_le (a a' : ℝ) (ha : 2 ≤ a) (haa' : a ≤ a') (ha' : a' ≤ 7 * a / 5) :
    Work.BMF.pi0 a' ≤ (7 / 5) * Work.BMF.pi0 a := by
  have hlog_a : 0 < Real.log a := Real.log_pos (by linarith)
  have hlog_a' : 0 < Real.log a' := Real.log_pos (by linarith)
  have hlog_le : Real.log a ≤ Real.log a' := Real.log_le_log (by linarith) haa'
  have h7a : (0 : ℝ) ≤ 7 * a / 5 := by linarith
  rw [Work.BMF.pi0, Work.BMF.pi0]
  calc a' / Real.log a' ≤ (7 * a / 5) / Real.log a' :=
        div_le_div_of_nonneg_right ha' hlog_a'.le
    _ ≤ (7 * a / 5) / Real.log a :=
        div_le_div_of_nonneg_left h7a hlog_a hlog_le
    _ = (7 / 5) * (a / Real.log a) := by field_simp

end Work.BMF.SD
