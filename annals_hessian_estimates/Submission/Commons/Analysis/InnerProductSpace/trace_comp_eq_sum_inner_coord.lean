import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem trace_comp_eq_sum_inner_coord {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) (F A : E →L[ℝ] E) :
    LinearMap.trace ℝ E ((F : E →ₗ[ℝ] E) ∘ₗ (A : E →ₗ[ℝ] E)) =
      ∑ i : ι, ∑ j : ι, ⟪F (v i), v j⟫ * ⟪A (v j), v i⟫ := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ v.toBasis]
  rw [LinearMap.toMatrix_comp v.toBasis v.toBasis v.toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [real_inner_comm ((F : E →ₗ[ℝ] E) (v i)) (v j),
    real_inner_comm ((A : E →ₗ[ℝ] E) (v j)) (v i)]
  rfl

end Commons.Analysis.InnerProductSpace