import Mathlib
import Submission.Work.HP.HP2.sum_Ico_rpow_neg_le

namespace Work.ClassCount

/-- For `s ≥ 3` the partial sums of `k ↦ k^{-s}` (with the `k = 0` term, which is `0`,
included) are bounded by `13/10`.  The proof compares each term with `k^{-3}` and then
splits off the terms `k = 0, 1` and bounds the tail `∑_{k=2}^{M-1} k^{-3}` by `1/4`
using the integral comparison `sum_Ico_rpow_neg_le`. -/
theorem zeta_partial_sum_le (s : ℝ) (hs : 3 ≤ s) (M : ℕ) :
    ∑ k ∈ Finset.range M, (k : ℝ) ^ (-s) ≤ 13 / 10 := by
  -- Termwise comparison with `k^{-3}`; the `k = 0` term is `0` on both sides.
  have hterm : ∀ k ∈ Finset.range M, (k : ℝ) ^ (-s) ≤ (k : ℝ) ^ (-3 : ℝ) := by
    intro k _
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [Nat.cast_zero]
      rw [Real.zero_rpow (by linarith : (-s : ℝ) ≠ 0),
          Real.zero_rpow (by norm_num : (-3 : ℝ) ≠ 0)]
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- Tail bound: `∑_{k=2}^{M-1} k^{-3} ≤ 1/4`.
  have htail : (∑ k ∈ Finset.Ico (2:ℕ) M, (k : ℝ) ^ (-3 : ℝ)) ≤ 1/4 := by
    have h := Work.HP.HP2.sum_Ico_rpow_neg_le 3 (by norm_num) 2 M (by norm_num)
    have h2 : (2:ℝ)^(-3:ℝ) + (2:ℝ)^(1-3:ℝ)/(3-1) = 1/4 := by norm_num
    linarith [h, h2]
  by_cases hM : M ≤ 2
  · -- `M ≤ 2`: the sum is `0` or `1`.
    interval_cases M <;> norm_num
  · -- `M ≥ 2`: split off the terms `k = 0, 1`.
    have hM2 : 2 ≤ M := by omega
    have hlow : (∑ k ∈ Finset.Ico (0:ℕ) 2, (k:ℝ)^(-3:ℝ)) = 1 := by norm_num
    have hdec := (Finset.sum_Ico_consecutive (fun k : ℕ => (k:ℝ)^(-3:ℝ))
        (by norm_num : (0:ℕ) ≤ 2) hM2).symm
    rw [Finset.range_eq_Ico, hdec, hlow]
    linarith [htail]

end Work.ClassCount
