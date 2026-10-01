import Mathlib
import Submission.Work.LinnikAreas.Density4.rpow_neg_three_halves_sum_le_four

namespace Work.LinnikAreas.Density4

/-- For every natural `d ≥ 1` the summand `1/(d·√d)` coincides with the real power
`d ^ (-(3/2))`.  This is because `3/2 = 1/2 + 1` and `d ^ (1/2) = √d`. -/
private lemma one_div_mul_sqrt_eq_rpow (d : ℕ) (hd : 1 ≤ d) :
    (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ)) = (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1 : ℝ) by norm_num, Real.rpow_add hd0]
  rw [Real.rpow_neg hd0.le, Real.rpow_div_two_eq_sqrt 1 hd0.le, Real.rpow_one,
    Real.rpow_neg_one]
  rw [one_div, mul_inv_rev]

/-- The partial sums of `1/(d·√d)` are bounded by `4`, hence by `6`.  Each summand
equals `d ^ (-(3/2))`, and the companion lemma
`rpow_neg_three_halves_sum_le_four` bounds the partial sums of that power by `4`. -/
theorem sum_inv_mul_sqrt_le (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ)) ≤ 6 := by
  calc ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))
      = ∑ d ∈ Finset.Icc 1 M, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact one_div_mul_sqrt_eq_rpow d (Finset.mem_Icc.mp hd).1
    _ ≤ 4 := rpow_neg_three_halves_sum_le_four M
    _ ≤ 6 := by norm_num

end Work.LinnikAreas.Density4
