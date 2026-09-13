import Mathlib
import Submission.Commons.Analysis.Sigma2.sigma2_sum_eq_coord_minor_sum

namespace Commons.Analysis.Sigma2

open scoped BigOperators
open scoped RealInnerProductSpace

/-! ## Elementary lemmas towards the expansion of `σ₂` of a sum

Throughout, `E` is a finite-dimensional real inner product space and `T : E →ₗ[ℝ] E` is a
symmetric endomorphism with eigenvalues `hT.eigenvalues hn : Fin n → ℝ` (where
`hn : Module.finrank ℝ E = n`).

The main results of this file are

* `sigma2_eigen_eq_trace_invariants_gen`: the pair sum `∑_{i < j} λᵢ λⱼ` of the eigenvalues of `T`
  equals `((tr T)² - tr (T ∘ T)) / 2` for *any* indexing `Fin n` (a generalisation of the
  `Fin (finrank ℝ E)` version already in the commons);
* `sigma2_eig_add_expansion`: the second elementary symmetric function of the eigenvalues of
  `A + M` expands as `σ₂(A) + σ₂(M) + tr A · tr M - tr (A ∘ M)`.
-/

/-- A triangular `Fin`-sum written in indicator form. -/
lemma sum_Iio_eq_sum_ite_fin {n : ℕ} {M : Type*} [AddCommMonoid M] (j : Fin n) (f : Fin n → M) :
    (∑ i < j, f i) = ∑ i : Fin n, if i < j then f i else 0 := by
  rw [show (∑ i < j, f i) = ∑ i ∈ Finset.Iio j, f i from rfl]
  rw [show Finset.Iio j = Finset.univ.filter (fun i => i < j) from by ext i; simp]
  rw [Finset.sum_filter]

/-- The pair sum `∑_{i<j} aᵢ aⱼ` expressed through the two power sums. -/
lemma pairSum_Iio_eq {n : ℕ} (a : Fin n → ℝ) :
    (∑ j : Fin n, ∑ i < j, a i * a j) =
      ((∑ i : Fin n, a i) ^ 2 - ∑ i : Fin n, (a i) ^ 2) / 2 := by
  have h : (∑ j : Fin n, ∑ i < j, a i * a j)
      = ∑ j : Fin n, ∑ i : Fin n, if i < j then a i * a j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    exact sum_Iio_eq_sum_ite_fin j (fun i => a i * a j)
  rw [h]
  exact pairSum_eq a

/-- `tr T = ∑ λᵢ`, for an arbitrary indexing of the eigenvalues by `Fin n`. -/
lemma trace_eq_sum_eigenvalues_gen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) :
    LinearMap.trace ℝ E T = ∑ i : Fin n, hT.eigenvalues hn i := by
  classical
  calc
    LinearMap.trace ℝ E T
        = Matrix.trace
            (LinearMap.toMatrix (hT.eigenvectorBasis hn).toBasis
              (hT.eigenvectorBasis hn).toBasis T) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ (hT.eigenvectorBasis hn).toBasis]
    _ = Matrix.trace (Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn)) := by
          rw [hT.toMatrix_eigenvectorBasis hn]
    _ = ∑ i : Fin n, hT.eigenvalues hn i := by
          rw [Matrix.trace_diagonal]
          simp

/-- `tr (T ∘ T) = ∑ λᵢ²`, for an arbitrary indexing of the eigenvalues by `Fin n`. -/
lemma trace_comp_self_eq_sum_eigenvalues_sq_gen {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    LinearMap.trace ℝ E (T ∘ₗ T) = ∑ i : Fin n, (hT.eigenvalues hn i) ^ 2 := by
  classical
  let b : Module.Basis (Fin n) ℝ E := (hT.eigenvectorBasis hn).toBasis
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn)
  have hmat : LinearMap.toMatrix b b T = D := by
    simpa [b, D] using
      (LinearMap.IsSymmetric.toMatrix_eigenvectorBasis (𝕜 := ℝ) (T := T) hT hn)
  calc
    LinearMap.trace ℝ E (T ∘ₗ T)
        = (LinearMap.toMatrix b b (T ∘ₗ T)).trace := by
          rw [LinearMap.trace_eq_matrix_trace ℝ b]
    _ = (LinearMap.toMatrix b b T * LinearMap.toMatrix b b T).trace := by
          rw [LinearMap.toMatrix_comp b b b T T]
    _ = (D * D).trace := by rw [hmat]
    _ = (Matrix.diagonal (fun i : Fin n =>
            (RCLike.ofReal (hT.eigenvalues hn i) * RCLike.ofReal (hT.eigenvalues hn i)))).trace := by
          dsimp [D]; rw [Matrix.diagonal_mul_diagonal]
    _ = ∑ i : Fin n,
          (RCLike.ofReal (hT.eigenvalues hn i) * RCLike.ofReal (hT.eigenvalues hn i)) := by
          rw [Matrix.trace_diagonal]
    _ = ∑ i : Fin n, (hT.eigenvalues hn i) ^ 2 := by simp [pow_two]

/-- The second elementary symmetric function of the eigenvalues of a symmetric endomorphism
`T`, expressed through the trace invariants `tr T` and `tr (T ∘ T)`. -/
lemma sigma2_eigen_eq_trace_invariants_gen {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    (∑ j : Fin n, ∑ i < j, hT.eigenvalues hn i * hT.eigenvalues hn j) =
      ((LinearMap.trace ℝ E T) ^ 2 - LinearMap.trace ℝ E (T ∘ₗ T)) / 2 := by
  rw [pairSum_Iio_eq (a := fun i => hT.eigenvalues hn i),
    trace_eq_sum_eigenvalues_gen hT hn, trace_comp_self_eq_sum_eigenvalues_sq_gen hT hn]

/-- Expansion of `tr ((F + G) ∘ (F + G))`. -/
lemma trace_comp_add_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F G : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E ((F + G) ∘ₗ (F + G)) =
      LinearMap.trace ℝ E (F ∘ₗ F) + 2 * LinearMap.trace ℝ E (F ∘ₗ G)
        + LinearMap.trace ℝ E (G ∘ₗ G) := by
  have h1 : (F + G) ∘ₗ (F + G) = F ∘ₗ F + F ∘ₗ G + (G ∘ₗ F + G ∘ₗ G) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
    abel
  rw [h1, map_add, map_add, map_add]
  rw [← LinearMap.trace_comp_comm' (f := G) (g := F)]
  ring

/-- **Expansion of `σ₂` of a sum of symmetric endomorphisms.**

For symmetric endomorphisms `S`, `T` of a finite-dimensional real inner product space `E` and any
indexing `hn : finrank ℝ E = n` of the eigenvalues, the second elementary symmetric function of
the eigenvalues of `S + T` expands as
`σ₂(S) + σ₂(T) + tr S · tr T - tr (S ∘ T)`.

This holds in every dimension `n`: it is the `n = 2` polarization identity for the two trace
invariants `σ₂(X) = ((tr X)² - tr (X ∘ X)) / 2`. -/
theorem sigma2_eig_add_expansion_gen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {S T : E →ₗ[ℝ] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    (∑ j : Fin n, ∑ i < j, (hS.add hT).eigenvalues hn i * (hS.add hT).eigenvalues hn j)
      = (∑ j : Fin n, ∑ i < j, hS.eigenvalues hn i * hS.eigenvalues hn j)
        + (∑ j : Fin n, ∑ i < j, hT.eigenvalues hn i * hT.eigenvalues hn j)
        + (LinearMap.trace ℝ E S * LinearMap.trace ℝ E T
           - LinearMap.trace ℝ E (S ∘ₗ T)) := by
  rw [sigma2_eigen_eq_trace_invariants_gen (hS.add hT) hn,
    sigma2_eigen_eq_trace_invariants_gen hS hn,
    sigma2_eigen_eq_trace_invariants_gen hT hn]
  have h1 : LinearMap.trace ℝ E (S + T)
      = LinearMap.trace ℝ E S + LinearMap.trace ℝ E T :=
    map_add (LinearMap.trace ℝ E) _ _
  have h2 : LinearMap.trace ℝ E ((S + T) ∘ₗ (S + T))
      = LinearMap.trace ℝ E (S ∘ₗ S) + 2 * LinearMap.trace ℝ E (S ∘ₗ T)
        + LinearMap.trace ℝ E (T ∘ₗ T) :=
    trace_comp_add_add _ _
  rw [h1, h2]
  ring

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem sigma2_eig_add_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A M : E →L[ℝ] E} (hA : A.IsSymmetric) (hM : M.IsSymmetric)
    (hn : Module.finrank ℝ E = 4) :
    (∑ j : Fin 4, ∑ i < j, (hA.add hM).eigenvalues hn i * (hA.add hM).eigenvalues hn j)
      = (∑ j : Fin 4, ∑ i < j, hA.eigenvalues hn i * hA.eigenvalues hn j)
        + (∑ j : Fin 4, ∑ i < j, hM.eigenvalues hn i * hM.eigenvalues hn j)
        + (LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) * LinearMap.trace ℝ E (M : E →ₗ[ℝ] E)
           - LinearMap.trace ℝ E ((A : E →ₗ[ℝ] E) ∘ₗ (M : E →ₗ[ℝ] E))) :=
  sigma2_eig_add_expansion_gen hA hM hn

end Commons.Analysis.Sigma2
