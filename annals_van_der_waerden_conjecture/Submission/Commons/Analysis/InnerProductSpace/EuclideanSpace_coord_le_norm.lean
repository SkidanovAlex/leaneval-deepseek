import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

theorem EuclideanSpace_coord_le_norm {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]
    (a : EuclideanSpace 𝕜 ι) (i : ι) : ‖a i‖ ≤ ‖a‖ := by
  have hsq : ‖a i‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖a j‖) (Finset.mem_univ i)
  have hnorm_nonneg_i : 0 ≤ ‖a i‖ := norm_nonneg _
  have hnorm_nonneg_a : 0 ≤ ‖a‖ := norm_nonneg _
  calc
    ‖a i‖ = Real.sqrt (‖a i‖ ^ 2) := (Real.sqrt_sq hnorm_nonneg_i).symm
    _ ≤ Real.sqrt (‖a‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖a‖ := Real.sqrt_sq hnorm_nonneg_a

end Commons.Analysis.InnerProductSpace