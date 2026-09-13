import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Trace

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace in
/-- For a self-adjoint (symmetric) positive-semidefinite operator `F` and an operator `A` whose
quadratic form is non-positive, the trace of the composition `F ∘ A` is non-positive.

The proof diagonalizes `F` in an orthonormal eigenbasis `b` with eigenvalues `λ i ≥ 0`. Writing the
trace in that basis, `trace (F ∘ A) = ∑ i ⟪b i, F (A (b i))⟫ = ∑ i λ i * ⟪b i, A (b i)⟫`, and each
term is `≤ 0` because `λ i ≥ 0` and `⟪b i, A (b i)⟫ = ⟪A (b i), b i⟫ ≤ 0`. -/
theorem trace_comp_nonpos_of_nonneg_nonpos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {F A : E →L[ℝ] E} (hF : F.IsSymmetric)
    (hFnn : ∀ x : E, 0 ≤ ⟪F x, x⟫) (hAnn : ∀ x : E, ⟪A x, x⟫ ≤ 0) :
    LinearMap.trace ℝ E ((F : E →ₗ[ℝ] E) ∘ₗ (A : E →ₗ[ℝ] E)) ≤ 0 := by
  classical
  -- The eigenvalues of `F` are non-negative.
  have hlam : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ hF.eigenvalues rfl i := by
    intro i
    refine eigenvalue_nonneg_of_nonneg (𝕜 := ℝ) (T := (F : E →ₗ[ℝ] E))
      (hF.hasEigenvalue_eigenvalues rfl i) (fun x => ?_)
    change 0 ≤ ⟪x, (F : E →ₗ[ℝ] E) x⟫
    rw [← hF x x]
    exact hFnn x
  calc
    LinearMap.trace ℝ E ((F : E →ₗ[ℝ] E) ∘ₗ (A : E →ₗ[ℝ] E))
        = ∑ i : Fin (Module.finrank ℝ E),
            ⟪hF.eigenvectorBasis rfl i,
              ((F : E →ₗ[ℝ] E) ∘ₗ (A : E →ₗ[ℝ] E)) (hF.eigenvectorBasis rfl i)⟫ := by
          rw [LinearMap.trace_eq_sum_inner _ (hF.eigenvectorBasis rfl)]
    _ = ∑ i : Fin (Module.finrank ℝ E),
            hF.eigenvalues rfl i * ⟪hF.eigenvectorBasis rfl i, A (hF.eigenvectorBasis rfl i)⟫ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [LinearMap.comp_apply]
          change ⟪hF.eigenvectorBasis rfl i,
              (F : E →ₗ[ℝ] E) (A (hF.eigenvectorBasis rfl i))⟫ =
            hF.eigenvalues rfl i * ⟪hF.eigenvectorBasis rfl i, A (hF.eigenvectorBasis rfl i)⟫
          rw [← hF (hF.eigenvectorBasis rfl i) (A (hF.eigenvectorBasis rfl i))]
          rw [hF.apply_eigenvectorBasis rfl i]
          rw [inner_smul_left]
          simp
    _ ≤ 0 := by
          apply Finset.sum_nonpos
          intro i _
          apply mul_nonpos_of_nonneg_of_nonpos (hlam i)
          rw [real_inner_comm]
          exact hAnn (hF.eigenvectorBasis rfl i)

end Commons.Analysis.InnerProductSpace