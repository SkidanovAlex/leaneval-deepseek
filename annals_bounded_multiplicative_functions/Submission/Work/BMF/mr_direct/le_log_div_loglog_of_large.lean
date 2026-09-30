import Mathlib
import Submission.Work.BMF.log_le_sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- For every `K > 0`, the quotient `log Y / log (log Y)` eventually dominates `K`:
with `t = log Y` we use `log t ≤ √t` (valid for `t ≥ 1`) and `√t ≥ K` (valid for
`t ≥ K²`), so that `K log t ≤ K √t ≤ √t · √t = t`, i.e. `K ≤ t / log t`. -/
theorem le_log_div_loglog_of_large (K : ℝ) (hK : 0 < K) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ Y : ℝ, X ≤ Y → K ≤ Real.log Y / Real.log (Real.log Y) := by
  refine ⟨Real.exp (max (K ^ 2) 2), ?_, ?_⟩
  · rw [Real.one_le_exp_iff]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right _ _)
  · intro Y hY
    have hXpos : 0 < Real.exp (max (K ^ 2) 2) := Real.exp_pos _
    have hYpos : 0 < Y := lt_of_lt_of_le hXpos hY
    have hlogY : max (K ^ 2) 2 ≤ Real.log Y := by
      rw [← Real.log_exp (max (K ^ 2) 2)]
      exact Real.log_le_log hXpos hY
    have hlogY1 : 1 ≤ Real.log Y :=
      le_trans (le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _)) hlogY
    have hKsq : K ^ 2 ≤ Real.log Y := le_trans (le_max_left _ _) hlogY
    have hlogtpos : 0 < Real.log (Real.log Y) := Real.log_pos (by
      have : (2 : ℝ) ≤ Real.log Y := le_trans (le_max_right _ _) hlogY
      linarith)
    have hlogYpos : 0 < Real.log Y := lt_of_lt_of_le zero_lt_one hlogY1
    have hsqrtK : K ≤ Real.sqrt (Real.log Y) := by
      have h1 : Real.sqrt (K ^ 2) ≤ Real.sqrt (Real.log Y) := Real.sqrt_le_sqrt hKsq
      rwa [Real.sqrt_sq (le_of_lt hK)] at h1
    have hle : Real.log (Real.log Y) ≤ Real.sqrt (Real.log Y) :=
      Work.BMF.log_le_sqrt_of_one_le (Real.log Y) hlogY1
    have hKlog : K * Real.log (Real.log Y) ≤ Real.log Y := by
      calc K * Real.log (Real.log Y) ≤ K * Real.sqrt (Real.log Y) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt hK)
        _ ≤ Real.sqrt (Real.log Y) * Real.sqrt (Real.log Y) :=
            mul_le_mul_of_nonneg_right hsqrtK (Real.sqrt_nonneg _)
        _ = Real.log Y := Real.mul_self_sqrt (le_of_lt hlogYpos)
    exact (le_div_iff₀ hlogtpos).mpr hKlog

end Work.BMF.mr_direct
