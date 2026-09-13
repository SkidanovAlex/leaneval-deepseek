import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Inequalities

theorem sum_pow_four_le_card_pow_three_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  exact pow_sum_le_card_mul_sum_pow hf 3

end Commons.Analysis.Inequalities