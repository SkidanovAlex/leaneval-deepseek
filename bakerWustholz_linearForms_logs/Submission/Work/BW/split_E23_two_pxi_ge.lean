import Mathlib
import Submission.Work.BW.split_E23_aux
import Submission.Work.BW.pxi_pow_pred_lower
import Submission.Work.BW.exp_neg_536_ge_05847

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `1.15 ≤ 2 · ξ^(r-1)` for `r ≥ 2`, where `ξ = pxi r = 1 - 0.536/r`.
Combines the lower bound `exp(-0.536) ≤ ξ^(r-1)` (from concavity of `log`)
with the numerical bound `0.5847 ≤ exp(-0.536)`. -/
theorem split_E23_two_pxi_ge {r : ℕ} (hr : 2 ≤ r) : (1.15:ℝ) ≤ 2 * (pxi r)^(r-1) := by
  have h1 : (0.5847 : ℝ) ≤ Real.exp (-0.536) := exp_neg_536_ge_05847
  have h2 : Real.exp (-0.536) ≤ (pxi r) ^ (r - 1) := pxi_pow_pred_lower hr
  linarith

end Work.BW
