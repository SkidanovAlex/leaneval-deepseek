import Mathlib
import Submission.Work.ANum3.PreludeA
import Submission.Work.ANum.HLog
import Submission.Work.ANum.tsum_log_geom_tail

/-! # The exponential bound `‖h(q)‖ ≤ 256‖q‖ e^{24‖q‖/(1-‖q‖)}`

For `‖q‖ < 1` the hauptmodul `h(q) = -256 q ∏'ₙ (1 + qⁿ⁺¹)²⁴` satisfies

  `‖h(q)‖ ≤ 256 ‖q‖ exp(24 ‖q‖/(1 - ‖q‖))`.

The proof writes `log ‖h(q)‖ = log 256 + log ‖q‖ + ∑ₙ 24 log ‖1 + qⁿ⁺¹‖`
(`Work.ANum.log_norm_hauptH_of_norm_lt_one`, valid for `q ≠ 0`), bounds each logarithmic term by
`‖qⁿ⁺¹‖` (`log ‖1 + z‖ ≤ ‖z‖`) and sums the resulting geometric series
(`Work.ANum.tsum_log_geom_tail`), then exponentiates. -/

namespace Work.ANum3

open scoped BigOperators

theorem hauptH_norm_le_exp {q : ℂ} (hq : ‖q‖ < 1) :
    ‖Submission.CDTPlan.hauptH q‖ ≤ 256 * ‖q‖ * Real.exp (24 * ‖q‖ / (1 - ‖q‖)) := by
  rcases eq_or_ne q 0 with rfl | hqne
  · simp [Submission.CDTPlan.hauptH]
  · have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hqne
    have hden : 0 < 1 - ‖q‖ := by linarith
    have hlogeq := Work.ANum.log_norm_hauptH_of_norm_lt_one (q := q) hq hqne
    have htsum : (∑' n : ℕ, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖) ≤ ‖q‖ / (1 - ‖q‖) := by
      have h := Work.ANum.tsum_log_geom_tail (q := q) (R := ‖q‖) (norm_nonneg q) hq le_rfl 0
      simpa [pow_one] using h
    have hlog_le : Real.log ‖Submission.CDTPlan.hauptH q‖
        ≤ Real.log 256 + Real.log ‖q‖ + 24 * ‖q‖ / (1 - ‖q‖) := by
      rw [hlogeq, tsum_mul_left]
      have h24 : 24 * (∑' n : ℕ, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖) ≤ 24 * ‖q‖ / (1 - ‖q‖) :=
        calc 24 * (∑' n : ℕ, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖)
            ≤ 24 * (‖q‖ / (1 - ‖q‖)) := mul_le_mul_of_nonneg_left htsum (by norm_num)
          _ = 24 * ‖q‖ / (1 - ‖q‖) := by rw [mul_div_assoc]
      linarith
    have hRHS_eq : Real.log (256 * ‖q‖ * Real.exp (24 * ‖q‖ / (1 - ‖q‖)))
        = Real.log 256 + Real.log ‖q‖ + 24 * ‖q‖ / (1 - ‖q‖) := by
      rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hqpos)) (Real.exp_ne_zero _),
        Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (ne_of_gt hqpos), Real.log_exp]
    have hRHSpos : 0 < 256 * ‖q‖ * Real.exp (24 * ‖q‖ / (1 - ‖q‖)) :=
      mul_pos (mul_pos (by norm_num) hqpos) (Real.exp_pos _)
    rcases eq_or_lt_of_le (norm_nonneg (Submission.CDTPlan.hauptH q)) with h0 | hpos
    · rw [← h0]; exact le_of_lt hRHSpos
    · calc ‖Submission.CDTPlan.hauptH q‖
          = Real.exp (Real.log ‖Submission.CDTPlan.hauptH q‖) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (Real.log (256 * ‖q‖ * Real.exp (24 * ‖q‖ / (1 - ‖q‖)))) :=
              Real.exp_le_exp.mpr (by rw [hRHS_eq]; exact hlog_le)
        _ = 256 * ‖q‖ * Real.exp (24 * ‖q‖ / (1 - ‖q‖)) := Real.exp_log hRHSpos

end Work.ANum3
