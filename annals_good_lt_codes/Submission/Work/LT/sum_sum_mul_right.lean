import Mathlib

namespace Work.LT

/-- Double-counting identity: summing `f (g * B j)` over all pairs `(g, j)` equals
`|ι|` times the total sum of `f`. For each `j`, right multiplication by `B j` is a
permutation of the finite group `G`, hence `∑ g, f (g * B j) = ∑ g, f g`. -/
theorem sum_sum_mul_right {G ι : Type*} [Group G] [Fintype G] [Fintype ι] (B : ι → G) (f : G → ℝ) :
    ∑ g, ∑ j : ι, f (g * B j) = (Fintype.card ι : ℝ) * ∑ g, f g := by
  have h : ∀ j : ι, ∑ g, f (g * B j) = ∑ g, f g := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (B j)) f]
    rfl
  rw [Finset.sum_comm]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Work.LT
