import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Inequalities

/-- The power-mean (Jensen) inequality for a finite set of nonnegative reals and an
exponent `r ≥ 1`: `(Σ f) ^ r ≤ |u|^{r-1} · Σ f ^ r`. -/
theorem sum_rpow_le_card_mul_sum_rpow {ι : Type*} (u : Finset ι) (f : ι → ℝ) (r : ℝ)
    (hf : ∀ i ∈ u, 0 ≤ f i) (hr : 1 ≤ r) :
    (∑ i ∈ u, f i) ^ r ≤ (u.card : ℝ) ^ (r - 1) * ∑ i ∈ u, f i ^ r := by
  simpa using Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := u) (f := f) (p := r) hr hf

end Commons.Analysis.Inequalities