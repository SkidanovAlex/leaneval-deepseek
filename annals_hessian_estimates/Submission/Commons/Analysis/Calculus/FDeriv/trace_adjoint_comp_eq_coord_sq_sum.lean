import Mathlib.Analysis.InnerProductSpace.Trace

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem trace_adjoint_comp_eq_coord_sq_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E)
    {T : E →L[ℝ] E} :
    LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E)) =
      ∑ i : ι, ∑ j : ι, ⟪T (v i), v j⟫ ^ 2 := by
  let S : E →ₗ[ℝ] E := (T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E)
  calc
    LinearMap.trace ℝ E S = ∑ i : ι, ⟪v i, S (v i)⟫ := by
      exact LinearMap.trace_eq_sum_inner S v
    _ = ∑ i : ι, ‖T (v i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [S, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    _ = ∑ i : ι, ∑ j : ι, ⟪T (v i), v j⟫ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (v.sum_sq_inner_left (T (v i))).symm

end Commons.Analysis.Calculus.FDeriv
