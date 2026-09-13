import Mathlib

namespace Commons.Analysis.Sigma2

/-! For a self-adjoint continuous linear operator `T : E →L[ℝ] E` on a finite-dimensional real inner product space, `trace(T.adjoint ∘ T) = trace(T ∘ T)`.  Since `T` is self-adjoint, `T.adjoint = T` (prove or use `LinearMap.IsSymmetric.clm_adjoint_eq`). -/
open scoped BigOperators

theorem trace_adjoint_sq_eq_trace_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric) :
    LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E).adjoint ∘ₗ (T : E →ₗ[ℝ] E)) =
      LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) := by
  have hA : (T : E →ₗ[ℝ] E).adjoint = (T : E →ₗ[ℝ] E) := by
    simpa using (LinearMap.IsSymmetric.adjoint_eq (A := (T : E →ₗ[ℝ] E)) hT)
  rw [hA]

end Commons.Analysis.Sigma2
