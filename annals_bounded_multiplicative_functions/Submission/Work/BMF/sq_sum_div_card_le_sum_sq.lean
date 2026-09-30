import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Cauchy–Schwarz / Chebyshev bound: the square of a sum divided by any `K` at least as large as
the cardinality of the indexing set is at most the sum of squares.

Indeed `(∑ g)^2 ≤ #s * ∑ g^2` (Cauchy–Schwarz), `#s ≤ K` and `∑ g^2 ≥ 0` give
`(∑ g)^2 ≤ K * ∑ g^2`, and dividing by `K > 0` yields the claim. -/
theorem sq_sum_div_card_le_sum_sq {ι : Type*} (s : Finset ι) (g : ι → ℝ) (K : ℝ)
    (hK : 0 < K) (hcard : (s.card : ℝ) ≤ K) :
    (∑ i ∈ s, g i) ^ 2 / K ≤ ∑ i ∈ s, g i ^ 2 := by
  have hS : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (∑ i ∈ s, g i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, g i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [div_le_iff₀ hK, mul_comm (∑ i ∈ s, g i ^ 2) K]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcard hS)

end Work.BMF
