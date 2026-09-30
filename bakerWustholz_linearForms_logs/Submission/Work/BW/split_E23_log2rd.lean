import Mathlib
import Submission.Work.BW.split_E23_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem split_E23_log2rd {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : Real.log (2*(r:ℝ)*d) ≤ (r:ℝ)*d*2 := by
  have hx : (0 : ℝ) ≤ 2 * (r : ℝ) * d := by positivity
  calc Real.log (2 * (r : ℝ) * d) ≤ 2 * (r : ℝ) * d := Real.log_le_self hx
    _ = (r : ℝ) * d * 2 := by ring

end Work.BW
