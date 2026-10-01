import Mathlib
import Submission.Work.LinnikAreas.Density4.rpow_neg_three_halves_sum_le_four

namespace Work.LinnikAreas.Density4

/-- Reindexing the summation range: the sum over `n ∈ Icc 2 N` of a function of
`n - 1` is the sum over the shifted range `range (N-1)` of the function of `k + 1`.
Both sides are empty for `N ≤ 1`. -/
private lemma sum_Icc_two_shift (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) - 1) ^ (3 / 2 : ℝ))
      = ∑ k ∈ Finset.range (N - 1), 1 / ((k : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  have hIcc2 : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc2, Finset.sum_Ico_eq_sum_range]
  rw [show N + 1 - 2 = N - 1 by omega]
  apply Finset.sum_congr rfl
  intro k hk
  have hb : ((2 + k : ℕ) : ℝ) - 1 = (k : ℝ) + 1 := by push_cast; ring
  rw [hb]

/-- The same reindexing on the other side: the sum over `Icc 1 (N-1)` in the form
`m ^ (-(3/2))` equals the sum over `range (N-1)` of `(k+1) ^ (-(3/2))`. -/
private lemma sum_Icc_one_shift (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 (N - 1), (m : ℝ) ^ (-(3 / 2 : ℝ)))
      = ∑ k ∈ Finset.range (N - 1), ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hIcc1 : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc1, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hb : ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hb]

/-- `1 / x ^ (3/2) = x ^ (-(3/2))` for `x ≥ 0`. -/
private lemma one_div_rpow_three_halves_eq (x : ℝ) (hx : 0 ≤ x) :
    1 / x ^ (3 / 2 : ℝ) = x ^ (-(3 / 2 : ℝ)) := by
  rw [one_div, ← Real.rpow_neg hx]

/-- The partial sums of `1/((n-1)^(3/2))` over `n ∈ Icc 2 N` are bounded by `4`.

Substituting `m = n - 1` turns the sum into `∑_{m=1}^{N-1} m ^ (-(3/2))`, which is
bounded by `4` by the companion lemma `rpow_neg_three_halves_sum_le_four`. -/
theorem dtb_sum_Icc_inv_pm1_rpow_le_four (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) - 1) ^ (3 / 2 : ℝ)) ≤ 4 := by
  have hmain : (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) - 1) ^ (3 / 2 : ℝ))
      = ∑ m ∈ Finset.Icc 1 (N - 1), (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [sum_Icc_two_shift, sum_Icc_one_shift]
    apply Finset.sum_congr rfl
    intro k hk
    exact one_div_rpow_three_halves_eq ((k : ℝ) + 1) (by positivity)
  rw [hmain]
  exact rpow_neg_three_halves_sum_le_four (N - 1)

end Work.LinnikAreas.Density4
