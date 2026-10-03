import Mathlib
import Submission.Work.FIArea7.divisor_sum_Icc_le

namespace Work.FIArea7

/-- Pointwise bound: the number of multiples of `d` in `[1, N]` is at most `N / d`,
whence at most `N * (1/d)` over the reals. -/
lemma card_multiples_Icc_cast_le (N d : ℕ) :
    ((((Finset.Icc 1 N).filter (fun b => d ∣ b)).card : ℕ) : ℝ)
      ≤ (N : ℝ) * (1 / (d : ℝ)) := by
  refine le_trans (Nat.cast_le.mpr (divisorSum_card_filter_dvd_Icc_le N d)) ?_
  have h : (N : ℝ) / (d : ℝ) = (N : ℝ) * (1 / (d : ℝ)) := by
    rw [one_div, div_eq_mul_inv]
  exact h ▸ Nat.cast_div_le

theorem sum_card_multiples_le_mul_harmonic (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ((((Finset.Icc 1 N).filter (fun b => d ∣ b)).card : ℕ) : ℝ))
      ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by
  calc (∑ d ∈ Finset.Icc 1 N, ((((Finset.Icc 1 N).filter (fun b => d ∣ b)).card : ℕ) : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 N, (N : ℝ) * (1 / (d : ℝ)) :=
        Finset.sum_le_sum (fun d _ => card_multiples_Icc_cast_le N d)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]

end Work.FIArea7
