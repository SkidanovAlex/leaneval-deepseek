import Mathlib

namespace Work.LT

/-- Expansion of a `Finset` sum of a product of two binomials: `∑ (c·A - B)(c·U - V)`
distributes into the four pairwise products. -/
theorem sum_quad_expand {ι : Type*} [Fintype ι] (A B U V : ι → ℝ) (c : ℝ) :
    (∑ x, (c * A x - B x) * (c * U x - V x))
      = c ^ 2 * (∑ x, A x * U x) - c * (∑ x, A x * V x)
          - c * (∑ x, B x * U x) + ∑ x, B x * V x := by
  have h : ∀ x, (c * A x - B x) * (c * U x - V x)
      = c^2 * (A x * U x) - c * (A x * V x) - c * (B x * U x) + B x * V x := by
    intro x; ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

end Work.LT
