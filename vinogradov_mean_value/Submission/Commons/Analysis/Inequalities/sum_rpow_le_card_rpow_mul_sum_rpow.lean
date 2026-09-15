import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Inequalities

open scoped NNReal ENNReal BigOperators

/-- **Hölder for a finite sum in `ℝ≥0∞`.** For `r ≥ 1` and a finite family `x : ι → ℝ≥0∞`,
the `r`-th power of the sum is bounded by `card^(r-1)` times the sum of the `r`-th powers. -/
theorem sum_rpow_le_card_rpow_mul_sum_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, x i) ^ r ≤ ((s.card : ℝ≥0∞)) ^ (r - 1) * ∑ i ∈ s, (x i) ^ r := by
  exact ENNReal.rpow_sum_le_const_mul_sum_rpow s x hr

end Commons.Analysis.Inequalities