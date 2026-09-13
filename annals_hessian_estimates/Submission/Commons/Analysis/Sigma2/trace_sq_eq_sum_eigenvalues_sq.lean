import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem trace_sq_eq_sum_eigenvalues_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric) :
    LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) =
      ∑ i : Fin (Module.finrank ℝ E), (hT.eigenvalues rfl i) ^ 2 := by
  classical
  let Tₗ : E →ₗ[ℝ] E := (T : E →ₗ[ℝ] E)
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := (hT.eigenvectorBasis rfl).toBasis
  let D : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues rfl)
  have hmat : LinearMap.toMatrix b b Tₗ = D := by
    simpa [Tₗ, b, D] using
      (LinearMap.IsSymmetric.toMatrix_eigenvectorBasis (𝕜 := ℝ) (T := Tₗ) hT rfl)
  calc
    LinearMap.trace ℝ E (Tₗ ∘ₗ Tₗ)
        = (LinearMap.toMatrix b b (Tₗ ∘ₗ Tₗ)).trace := by
          rw [LinearMap.trace_eq_matrix_trace ℝ b]
    _ = (LinearMap.toMatrix b b Tₗ * LinearMap.toMatrix b b Tₗ).trace := by
          rw [LinearMap.toMatrix_comp b b b Tₗ Tₗ]
    _ = (D * D).trace := by
          rw [hmat]
    _ = (Matrix.diagonal (fun i : Fin (Module.finrank ℝ E) =>
            (RCLike.ofReal (hT.eigenvalues rfl i) * RCLike.ofReal (hT.eigenvalues rfl i)))).trace := by
          dsimp [D]
          rw [Matrix.diagonal_mul_diagonal]
    _ = ∑ i : Fin (Module.finrank ℝ E),
            (RCLike.ofReal (hT.eigenvalues rfl i) * RCLike.ofReal (hT.eigenvalues rfl i)) := by
          rw [Matrix.trace_diagonal]
    _ = ∑ i : Fin (Module.finrank ℝ E), (hT.eigenvalues rfl i) ^ 2 := by
          simp [pow_two]

end Commons.Analysis.Sigma2