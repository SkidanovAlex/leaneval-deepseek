import Mathlib
import Submission.Commons.Analysis.ExpLog.tail_pow_exp_neg_bound_exists
import Submission.Commons.Analysis.ExpLog.integral_comp_exp_pow_log_sqrt
import Submission.Commons.Analysis.ExpLog.exp_neg_log_half_eq_inv_sqrt

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Commons.Analysis.Real

lemma one_le_log_of_exp_one_le {x : ℝ} (h : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h
  have hlog : Real.log (Real.exp 1) ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h
  simpa using hlog

theorem tail_integral_log10 :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, Real.exp 1 ≤ x →
      (∫ t in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t)) ≤
        K * (Real.log x) ^ 10 / Real.sqrt x := by
  rcases Commons.Analysis.ExpLog.tail_pow_exp_neg_bound_exists with ⟨K, hKpos, hKbound⟩
  refine ⟨K, hKpos, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog : 1 ≤ Real.log x := one_le_log_of_exp_one_le hx
  calc
    (∫ t in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t))
        = ∫ u : ℝ in Set.Ioi (Real.log x), u ^ 10 * Real.exp (-(u / 2)) :=
            Commons.Analysis.ExpLog.integral_comp_exp_pow_log_sqrt hxpos
    _ ≤ K * (Real.log x) ^ 10 * Real.exp (-(Real.log x / 2)) :=
            hKbound (Real.log x) hlog
    _ = K * (Real.log x) ^ 10 * Real.exp (-(Real.log x) / 2) := by
          have harg : -(Real.log x) / 2 = -(Real.log x / 2) := by ring
          rw [← harg]
    _ = K * (Real.log x) ^ 10 / Real.sqrt x := by
          rw [Commons.Analysis.ExpLog.exp_neg_log_half_eq_inv_sqrt hxpos]
          ring

end Commons.Analysis.Real
