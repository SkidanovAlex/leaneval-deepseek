import Mathlib
import Submission.Work.LT.relT_defs

namespace Work.LT

open scoped Real

/-- `l2norm h = √(∑ x, Complex.normSq (h x))` agrees with the `ℓ²` norm of the element
`WithLp.toLp 2 h` of the Euclidean space `EuclideanSpace ℂ X`. -/
lemma l2norm_eq_norm {X : Type*} [Fintype X] (h : X → ℂ) :
    l2norm h = ‖(WithLp.toLp 2 h : EuclideanSpace ℂ X)‖ := by
  rw [l2norm, l2sq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.normSq_eq_norm_sq]

/-- Minkowski (triangle) inequality for the `ℓ²`-norm `l2norm h = √(∑ x, Complex.normSq (h x))` of a
complex-valued function on a finite type. -/
theorem l2norm_triangle {X : Type*} [Fintype X] (a b : X → ℂ) :
    l2norm (a + b) ≤ l2norm a + l2norm b := by
  rw [l2norm_eq_norm (a + b), l2norm_eq_norm a, l2norm_eq_norm b, WithLp.toLp_add]
  exact norm_add_le _ _

end Work.LT
