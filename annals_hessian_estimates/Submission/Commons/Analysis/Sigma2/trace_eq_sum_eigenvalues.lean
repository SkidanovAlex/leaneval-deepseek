import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem trace_eq_sum_eigenvalues {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric) :
    LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) =
      ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i := by
  classical
  calc
    LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)
        = Matrix.trace
            (LinearMap.toMatrix (hT.eigenvectorBasis rfl).toBasis
              (hT.eigenvectorBasis rfl).toBasis (T : E →ₗ[ℝ] E)) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ (hT.eigenvectorBasis rfl).toBasis]
    _ = Matrix.trace (Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues rfl)) := by
          rw [hT.toMatrix_eigenvectorBasis rfl]
    _ = ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i := by
          rw [Matrix.trace_diagonal]
          simp

end Commons.Analysis.Sigma2