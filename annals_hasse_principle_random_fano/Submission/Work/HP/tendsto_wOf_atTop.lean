import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- `t / log t → ∞` as `t → ∞`: the log is eventually dominated by any positive
fraction of the identity, so the ratio grows without bound. -/
lemma tendsto_log_div_log_atTop :
    Filter.Tendsto (fun t : ℝ => t / Real.log t) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro a
  rw [Filter.eventually_atTop]
  set M := max a 1 with hM
  have haM : a ≤ M := le_max_left _ _
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨max (4 * M ^ 2) (Real.exp 1), fun t ht => ?_⟩
  have ht4 : 4 * M ^ 2 ≤ t := le_trans (le_max_left _ _) ht
  have hte : Real.exp 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) hte
  have hlogt_ge1 : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) hte
    rwa [Real.log_exp] at h
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le one_pos hlogt_ge1
  -- `log t ≤ 2 √t`, so `t / (2√t) ≤ t / log t`
  have hbound : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 := Real.log_le_rpow_div (le_of_lt htpos) (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : t ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * Real.sqrt t := by
      rw [Real.sqrt_eq_rpow]; ring
    linarith
  have hdiv : t / (2 * Real.sqrt t) ≤ t / Real.log t :=
    div_le_div_of_nonneg_left (le_of_lt htpos) hlogtpos hbound
  -- `2M ≤ √t`, so `M ≤ t / (2√t)`
  have hsqrt : 2 * M ≤ Real.sqrt t := by
    have h4 : Real.sqrt (4 * M ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt ht4
    have hsq : Real.sqrt (4 * M ^ 2) = 2 * M := by
      have he : (4 : ℝ) * M ^ 2 = (2 * M) * (2 * M) := by ring
      rw [he, Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ 2 * M)]
    linarith
  have htdiv : t / (2 * Real.sqrt t) = Real.sqrt t / 2 := by
    have hsq := Real.sq_sqrt (le_of_lt htpos)
    have hs : Real.sqrt t ≠ 0 := by positivity
    field_simp
    nlinarith
  have hMt : M ≤ t / (2 * Real.sqrt t) := by rw [htdiv]; linarith
  linarith [haM, hMt, hdiv]

theorem tendsto_wOf_atTop : Filter.Tendsto wOf Filter.atTop Filter.atTop := by
  have h := tendsto_log_div_log_atTop.comp Real.tendsto_log_atTop
  unfold wOf
  exact h

end Work.HP
