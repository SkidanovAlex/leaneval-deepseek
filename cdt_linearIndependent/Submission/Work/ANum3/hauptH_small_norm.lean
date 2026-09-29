import Mathlib
import Submission.Work.ANum3.PreludeA
import Submission.Work.ANum.HLog
import Submission.Work.ANum.tsum_log_geom_tail

/-! # `‖h(q)‖ ≤ 4` on the disc `‖q‖ ≤ 1/100`

The hauptmodul `h(q) = -256 q ∏'ₙ (1 + qⁿ⁺¹)²⁴` of `Submission.CDTPlan` is small near the origin.
Writing `log ‖h(q)‖ = log 256 + log ‖q‖ + ∑ₙ 24 log ‖1 + qⁿ⁺¹‖` (convergent for `‖q‖ < 1`) and
bounding each `log ‖1 + z‖ ≤ ‖z‖` gives, for `‖q‖ ≤ 1/100`,

  `log ‖h(q)‖ ≤ log 256 + log(1/100) + 24/99 ≤ log 4`,

since `24/99 ≤ 1 - 16/25 ≤ log(25/16)` and `(256/100)·(25/16) = 4`. -/

namespace Work.ANum3

open scoped BigOperators

theorem hauptH_small_norm {q : ℂ} (hq : ‖q‖ ≤ 1 / 100) : ‖Submission.CDTPlan.hauptH q‖ ≤ 4 := by
  have hq1 : ‖q‖ < 1 := by linarith
  rcases eq_or_ne q 0 with rfl | hqne
  · simp [Submission.CDTPlan.hauptH]
  · have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hqne
    have hlogeq := Work.ANum.log_norm_hauptH_of_norm_lt_one (q := q) hq1 hqne
    -- the logarithmic series is dominated by the geometric series `∑ ‖q‖ⁿ⁺¹ = ‖q‖/(1-‖q‖)`
    have htsum : (∑' n : ℕ, 24 * Real.log ‖(1 : ℂ) + q ^ (n + 1)‖)
        ≤ 24 * (‖q‖ / (1 - ‖q‖)) := by
      rw [tsum_mul_left]
      have h := Work.ANum.tsum_log_geom_tail (q := q) (R := ‖q‖) (norm_nonneg q) hq1 le_rfl 0
      have h' : (∑' n : ℕ, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖) ≤ ‖q‖ / (1 - ‖q‖) := by
        simpa [pow_one] using h
      exact mul_le_mul_of_nonneg_left h' (by norm_num)
    have hratio : ‖q‖ / (1 - ‖q‖) ≤ (1 : ℝ) / 99 := by
      have hden : (0 : ℝ) < 1 - ‖q‖ := by have := norm_nonneg q; linarith
      rw [div_le_iff₀ hden]
      nlinarith [norm_nonneg q, hq]
    have htsum2 : (∑' n : ℕ, 24 * Real.log ‖(1 : ℂ) + q ^ (n + 1)‖) ≤ 24 / 99 :=
      calc _ ≤ 24 * (‖q‖ / (1 - ‖q‖)) := htsum
        _ ≤ 24 * ((1 : ℝ) / 99) := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = 24 / 99 := by norm_num
    have hlogq : Real.log ‖q‖ ≤ Real.log (1 / 100) := Real.log_le_log hqpos hq
    have hnum : Real.log 256 + Real.log (1 / 100 : ℝ) + 24 / 99 ≤ Real.log 4 := by
      have h64 : Real.log 256 + Real.log (1 / 100 : ℝ) = Real.log (64 / 25) := by
        rw [← Real.log_mul (by norm_num : (256 : ℝ) ≠ 0)
          (by norm_num : ((1 : ℝ) / 100) ≠ 0)]
        norm_num
      have hsplit : Real.log (4 : ℝ) = Real.log (64 / 25) + Real.log (25 / 16) := by
        rw [← Real.log_mul (by norm_num : (64 / 25 : ℝ) ≠ 0)
          (by norm_num : (25 / 16 : ℝ) ≠ 0)]
        norm_num
      have hlow : (24 : ℝ) / 99 ≤ Real.log (25 / 16) :=
        le_trans (by norm_num)
          (Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 25 / 16))
      rw [hsplit, h64]
      linarith
    have hchain : Real.log ‖Submission.CDTPlan.hauptH q‖ ≤ Real.log 4 := by
      rw [hlogeq]
      linarith [hlogq, htsum2, hnum]
    rcases eq_or_lt_of_le (norm_nonneg (Submission.CDTPlan.hauptH q)) with h | h
    · rw [← h]; norm_num
    · exact (Real.log_le_log_iff h (by norm_num : (0 : ℝ) < 4)).mp hchain

end Work.ANum3
