import Mathlib
import Submission.Work.BMF.mr_core_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- `log Pc Y = logPc Y` (the exponential in `Pc` is inverted). -/
lemma log_Pc (Y : ℝ) : Real.log (Work.BMF.mrCore.Pc Y) = Work.BMF.mrCore.logPc Y := by
  rw [Work.BMF.mrCore.Pc, Real.log_exp]

/-- `log Qc B Y = logQc B Y`. -/
lemma log_Qc (B Y : ℝ) : Real.log (Work.BMF.mrCore.Qc B Y) = Work.BMF.mrCore.logQc B Y := by
  rw [Work.BMF.mrCore.Qc, Real.log_exp]

/-- `logPc Y = (log Y)^{47/48}` is positive as soon as `Y > 1`. -/
lemma logPc_pos {Y : ℝ} (hY : 1 < Y) : 0 < Work.BMF.mrCore.logPc Y := by
  rw [Work.BMF.mrCore.logPc]
  exact Real.rpow_pos_of_pos (Real.log_pos hY) _

theorem bpcell_logratio {B Y : ℝ} (hY : (16 : ℝ) ^ 8 ≤ Y) :
    Real.log (Work.BMF.mrCore.Qc B Y) / Real.log (Work.BMF.mrCore.Pc Y)
      = Work.BMF.mrCore.Ac B := by
  have hY1 : (1 : ℝ) < Y := by
    have h : (1 : ℝ) < (16 : ℝ) ^ 8 := by norm_num
    linarith
  have hpos : 0 < Work.BMF.mrCore.logPc Y := logPc_pos hY1
  rw [log_Qc, log_Pc, Work.BMF.mrCore.logQc]
  exact mul_div_cancel_right₀ _ (ne_of_gt hpos)

end Work.BMF.mr_core
