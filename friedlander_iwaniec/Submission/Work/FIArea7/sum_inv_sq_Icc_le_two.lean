import Mathlib
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable

namespace Work.FIArea7

/-- The full tail `∑_{n ≥ 1} 1/n²` is at most `2`, since it is dominated by the telescoping
series `∑ (1/(n - 1/2) - 1/(n + 1/2))` whose value is `2`.  The `Icc 1 X` sum is a
sub-sum of this tail. -/
theorem sum_inv_sq_Icc_le_two (X : ℕ) :
    (∑ b ∈ Finset.Icc 1 X, (1:ℝ) / (b : ℝ) ^ 2) ≤ 2 := by
  have hsum : (∑ b ∈ Finset.Icc 1 X, (1:ℝ) / (b : ℝ) ^ 2)
      ≤ ∑' n : ℕ, (if 1 ≤ n then (1:ℝ) / (n : ℝ) ^ 2 else 0) := by
    have hcongr : (∑ b ∈ Finset.Icc 1 X, (1:ℝ) / (b : ℝ) ^ 2)
        = ∑ b ∈ Finset.Icc 1 X, (if 1 ≤ b then (1:ℝ) / (b : ℝ) ^ 2 else 0) := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [Finset.mem_Icc] at hb
      rw [if_pos hb.1]
    rw [hcongr]
    exact Summable.sum_le_tsum _ (fun n _ => by split <;> positivity)
      (Commons.Analysis.Series.tail_inv_sq_summable 1)
  have htsum := Commons.Analysis.Series.tail_inv_sq_le 1 le_rfl
  have h2 : (2:ℝ) / (2 * ((1:ℕ):ℝ) - 1) = 2 := by norm_num
  linarith [htsum, hsum]

end Work.FIArea7
