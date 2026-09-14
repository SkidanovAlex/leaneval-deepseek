import Mathlib
import Submission.Commons.Analysis.Series.sum_inv_mul_sqrt_le_three

namespace Commons.Analysis.Series

/-- Reindex a sum over `Finset.Icc 1 n` as a sum over `Finset.range n`
(shifting the index by one). -/
lemma sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (n : ℕ) :
    (∑ b ∈ Finset.Icc 1 n, g b) = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega) g, ih, Finset.sum_range_succ]

theorem sum_Icc_inv_mul_sqrt_le_three (n : ℕ) :
    (∑ b ∈ Finset.Icc 1 n, (1:ℝ) / ((b:ℝ) * Real.sqrt b)) ≤ 3 := by
  calc (∑ b ∈ Finset.Icc 1 n, (1:ℝ) / ((b:ℝ) * Real.sqrt b))
      = ∑ k ∈ Finset.range n,
          (1:ℝ) / ((((k + 1 : ℕ)) : ℝ) * Real.sqrt (((k + 1 : ℕ)) : ℝ)) :=
        sum_Icc_one_eq_sum_range _ n
    _ = ∑ k ∈ Finset.range n, (1:ℝ) / ((k + 1 : ℝ) * Real.sqrt (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        simp [Nat.cast_add, Nat.cast_one]
    _ ≤ 3 := sum_inv_mul_sqrt_le_three n

end Commons.Analysis.Series
