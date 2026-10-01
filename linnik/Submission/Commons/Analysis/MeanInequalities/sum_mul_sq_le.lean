import Mathlib.Algebra.Order.Star.Real

set_option linter.unusedVariables false

namespace Commons.Analysis.MeanInequalities

open Finset

/-- Cauchy–Schwarz in squared form: for nonnegative `A`, `M` and any `k ≥ 0`,
`(∑ A_i M_i^k)^2 ≤ (∑ A_i^2) * ∑ A_i^0 * (M_i^k)^2`, specialised to
`(∑ A_i M_i^k)^2 ≤ (∑ A_i^2) * (∑ (M_i^k)^2)`. -/
theorem sum_mul_sq_le {ι : Type*} (s : Finset ι) (A M : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hM : ∀ i ∈ s, 0 ≤ M i) (k : ℕ) :
    (∑ i ∈ s, A i * (M i) ^ k) ^ 2 ≤ (∑ i ∈ s, A i ^ 2) * ∑ i ∈ s, ((M i) ^ k) ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s A (fun i => (M i) ^ k)

end Commons.Analysis.MeanInequalities