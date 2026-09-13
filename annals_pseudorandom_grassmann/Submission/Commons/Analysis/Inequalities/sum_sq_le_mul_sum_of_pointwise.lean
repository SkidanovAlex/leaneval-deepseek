import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Inequalities

/-- Given pointwise `a i ^ 2 ≤ b i * c i` with `b i, c i ≥ 0`, the sums satisfy
`(∑ a i)^2 ≤ (∑ b i) * (∑ c i)`. This is Cauchy–Schwarz stated via the pointwise
bound on the sequences `b`, `c`. -/
theorem sum_sq_le_mul_sum_of_pointwise {ι : Type*} [Fintype ι] (a b c : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (h : ∀ i, a i ^ 2 ≤ b i * c i) :
    (∑ i, a i) ^ 2 ≤ (∑ i, b i) * (∑ i, c i) := by
  simpa using Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (fun i _ => hb i) (fun i _ => hc i) (fun i _ => h i)

end Commons.Analysis.Inequalities