import Mathlib
import Submission.Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one

namespace Commons.NumberTheory.Sieve

/-- The sum over primes `p ≤ z` of `log p / p ^ 2` is bounded uniformly in `z`. -/
theorem sum_primes_log_div_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ,
      (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤ C := by
  obtain ⟨hsum, htsum⟩ :=
    Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
    fun n => div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  refine ⟨1, one_pos, fun z => ?_⟩
  calc
    (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Icc 1 z, Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro x hx hxs
          exact hnonneg x
    _ ≤ ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
          hsum.sum_le_tsum (Finset.Icc 1 z) (fun n _ => hnonneg n)
    _ ≤ 1 := htsum

end Commons.NumberTheory.Sieve
