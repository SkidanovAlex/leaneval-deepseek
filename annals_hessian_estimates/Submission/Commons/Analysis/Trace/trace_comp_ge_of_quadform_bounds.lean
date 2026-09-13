import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Trace

namespace Commons.Analysis.Trace

open scoped BigOperators in
open scoped RealInnerProductSpace in
/-- For a self-adjoint (symmetric) positive-semidefinite operator `A` and an operator `F` whose
quadratic form is non-negative, the trace of the composition `A ∘ F` is non-negative.

The proof diagonalizes `A` in an orthonormal eigenbasis `b` with eigenvalues `λ i ≥ 0`. Writing the
trace in that basis, `trace (A ∘ F) = ∑ i ⟪b i, A (F (b i))⟫ = ∑ i λ i * ⟪b i, F (b i)⟫`, and each
term is `≥ 0` because `λ i ≥ 0` and `⟪b i, F (b i)⟫ ≥ 0`. -/
theorem trace_comp_nonneg_of_nonneg_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {A F : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hAnn : ∀ x : E, 0 ≤ ⟪A x, x⟫) (hFnn : ∀ x : E, 0 ≤ ⟪F x, x⟫) :
    0 ≤ LinearMap.trace ℝ E (A ∘ₗ F) := by
  classical
  -- The eigenvalues of `A` are non-negative.
  have hlam : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ hA.eigenvalues rfl i := by
    intro i
    refine eigenvalue_nonneg_of_nonneg (𝕜 := ℝ) (T := A)
      (hA.hasEigenvalue_eigenvalues rfl i) (fun x => ?_)
    change 0 ≤ ⟪x, A x⟫
    rw [← hA x x]
    exact hAnn x
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      0 ≤ hA.eigenvalues rfl i
        * ⟪hA.eigenvectorBasis rfl i, F (hA.eigenvectorBasis rfl i)⟫ := by
    intro i
    refine mul_nonneg (hlam i) ?_
    rw [real_inner_comm]
    exact hFnn _
  calc
    (0 : ℝ)
        ≤ ∑ i : Fin (Module.finrank ℝ E),
            hA.eigenvalues rfl i
              * ⟪hA.eigenvectorBasis rfl i, F (hA.eigenvectorBasis rfl i)⟫ :=
          Finset.sum_nonneg (fun i _ => hterm i)
    _ = ∑ i : Fin (Module.finrank ℝ E),
            ⟪hA.eigenvectorBasis rfl i, (A ∘ₗ F) (hA.eigenvectorBasis rfl i)⟫ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [LinearMap.comp_apply,
            ← hA (hA.eigenvectorBasis rfl i) (F (hA.eigenvectorBasis rfl i)),
            hA.apply_eigenvectorBasis rfl i, inner_smul_left]
          simp
    _ = LinearMap.trace ℝ E (A ∘ₗ F) := by
          rw [LinearMap.trace_eq_sum_inner _ (hA.eigenvectorBasis rfl)]

open scoped RealInnerProductSpace in
theorem trace_comp_ge_of_quadform_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {C N : E →L[ℝ] E}
    (hC : C.IsSymmetric) (hN : N.IsSymmetric) {c₁ : ℝ}
    (h1 : ∀ v : E, c₁ * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) (hNpos : ∀ v : E, 0 ≤ ⟪N v, v⟫) :
    c₁ * LinearMap.trace ℝ E (N : E →ₗ[ℝ] E)
      ≤ LinearMap.trace ℝ E ((C : E →ₗ[ℝ] E) ∘ₗ (N : E →ₗ[ℝ] E)) := by
  classical
  -- The operator `A = C - c₁ • 1` is symmetric and positive semi-definite.
  set A : E →ₗ[ℝ] E := (C : E →ₗ[ℝ] E) - c₁ • (1 : E →ₗ[ℝ] E) with hAdef
  have hAsym : A.IsSymmetric := by
    rw [hAdef]
    exact hC.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one)
  have hAnn : ∀ v : E, 0 ≤ ⟪A v, v⟫ := by
    intro v
    have hv : c₁ * ‖v‖ ^ 2 ≤ ⟪(C : E →ₗ[ℝ] E) v, v⟫ := h1 v
    rw [hAdef]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_eq_id,
      LinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    linarith
  -- Hence `trace (A ∘ N) ≥ 0`.
  have hkey : 0 ≤ LinearMap.trace ℝ E (A ∘ₗ (N : E →ₗ[ℝ] E)) :=
    trace_comp_nonneg_of_nonneg_nonneg hAsym hAnn hNpos
  -- Decompose `C = A + c₁ • 1` to relate the two traces.
  have hCeq : (C : E →ₗ[ℝ] E) = A + c₁ • (1 : E →ₗ[ℝ] E) := by
    rw [hAdef]; abel
  have hdec : LinearMap.trace ℝ E ((C : E →ₗ[ℝ] E) ∘ₗ (N : E →ₗ[ℝ] E))
      = LinearMap.trace ℝ E (A ∘ₗ (N : E →ₗ[ℝ] E))
        + c₁ * LinearMap.trace ℝ E (N : E →ₗ[ℝ] E) := by
    rw [hCeq, LinearMap.add_comp, LinearMap.smul_comp, Module.End.one_eq_id,
      LinearMap.id_comp, map_add, map_smul, smul_eq_mul]
  linarith [hkey, hdec]

end Commons.Analysis.Trace