import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

/-- The `ℓ²` norm of a vector in `EuclideanSpace ℝ ι` is dominated by the `ℓ¹` norm of its
coordinates: `‖x‖ ≤ ∑ i, |x i|`.  This is the elementary inequality
`(∑ xᵢ)² = ∑ xᵢ² + 2 ∑_{i<j} xᵢxⱼ ≥ ∑ xᵢ²` for the squared norms. -/
theorem norm_le_sum_abs_coord {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  simpa [Real.norm_eq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i : ι => |x i|)
      (fun i _ => abs_nonneg _))

end Commons.Analysis.InnerProductSpace
