import Mathlib
import Submission.Work.LinnikAreas.Density4.ThetaLogsumDefs

namespace Work.LinnikAreas.Density4

/-- `tgH σ A t = t^(σ-1) * exp(-t/A)` is antitone on `(0, ∞)` for `σ ≤ 1` and `A > 0`:
both factors are positive and decreasing in `t`. -/
lemma tgH_antitone (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : tgH σ A t ≤ tgH σ A s := by
  unfold tgH
  have hone : 0 < s ^ (σ - 1) := Real.rpow_pos_of_pos hs _
  have hle1 : t ^ (σ - 1) ≤ s ^ (σ - 1) := Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  have hle2 : Real.exp (-t / A) ≤ Real.exp (-s / A) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    linarith [div_le_div_of_nonneg_right hst (le_of_lt hA)]
  exact mul_le_mul hle1 hle2 (le_of_lt (Real.exp_pos _)) (le_of_lt hone)

end Work.LinnikAreas.Density4
