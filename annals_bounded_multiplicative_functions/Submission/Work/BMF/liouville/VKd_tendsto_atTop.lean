import Mathlib
import Submission.Work.BMF.VKdenom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Filter

/-- As `y → ∞`, `(log y)^{2/3} → ∞`. -/
lemma tendsto_log_rpow_two_thirds :
    Filter.Tendsto (fun y : ℝ => (Real.log y) ^ (2 / 3 : ℝ)) Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp Real.tendsto_log_atTop

/-- As `y → ∞`, `(log log y)^{1/3} → ∞`. -/
lemma tendsto_loglog_rpow_one_third :
    Filter.Tendsto (fun y : ℝ => (Real.log (Real.log y)) ^ (1 / 3 : ℝ))
      Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)

theorem VKd_tendsto_atTop : Filter.Tendsto Work.BMF.VKd Filter.atTop Filter.atTop := by
  have h := tendsto_log_rpow_two_thirds.atTop_mul_atTop₀ tendsto_loglog_rpow_one_third
  change Filter.Tendsto
    (fun y : ℝ => (Real.log y) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ))
    Filter.atTop Filter.atTop
  exact h

end Work.BMF.liouville
