import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.trace_comp_eq_sum_inner_coord
import Submission.Commons.Analysis.Sigma2.sigma2_sum_eq_coord_minor_sum

namespace Commons.Analysis.Sigma2

open scoped BigOperators
open scoped RealInnerProductSpace

/-! ## The mixed coordinate minor sum is a trace invariant

For two self-adjoint endomorphisms `A`, `M` of a finite-dimensional real inner product
space and an orthonormal basis `b`, the "mixed" pair sum

`∑_{i<j} (A_{ii} M_{jj} + M_{ii} A_{jj} - 2 A_{ij} M_{ij})`

of their coordinate matrices `A_{ij} = ⟪A bᵢ, bⱼ⟫`, `M_{ij} = ⟪M bᵢ, bⱼ⟫` equals
`(tr A)(tr M) - tr (A ∘ M) = tr(((tr A)·1 - A) ∘ M)`.

This is the polarisation of `∑_{i<j} (A_{ii}A_{jj} - A_{ij}²) = (tr A² - tr (A∘A))/2`
and the mixed term in the expansion of `σ₂(A + M)`.

The first part is pure finite combinatorics, stated for a general index type `Fin n`.
-/

/-- Splitting a subtracted pair sum into the difference of the two triangular sums. -/
private lemma sum_ite_sub_two {n : ℕ} (X Y : Fin n → Fin n → ℝ) :
    (∑ j : Fin n, ∑ i : Fin n, if i < j then (X i j - 2 * Y i j) else 0)
      = (∑ j : Fin n, ∑ i : Fin n, if i < j then X i j else 0)
        - 2 * (∑ j : Fin n, ∑ i : Fin n, if i < j then Y i j else 0) := by
  have hpt : ∀ i j : Fin n, (if i < j then (X i j - 2 * Y i j) else 0)
      = (if i < j then X i j else 0) - 2 * (if i < j then Y i j else 0) := by
    intro i j; by_cases h : i < j <;> simp [h]
  have h1 : (∑ j : Fin n, ∑ i : Fin n, if i < j then (X i j - 2 * Y i j) else 0)
      = ∑ j : Fin n, ∑ i : Fin n,
          ((if i < j then X i j else 0) - 2 * (if i < j then Y i j else 0)) := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    exact hpt i j
  rw [h1]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Combinatorial core.** For two symmetric matrices `a`, `m` of size `n`, the triangular
mixed sum `∑_{i<j} (aᵢᵢ mⱼⱼ + mᵢᵢ aⱼⱼ - 2 aᵢⱼ mᵢⱼ)` is the polarization
`(∑ aᵢᵢ)(∑ mᵢᵢ) - ∑ᵢⱼ aᵢⱼ mᵢⱼ` of the two trace invariants. -/
theorem pair_mixed_eq {n : ℕ} (a m : Fin n → Fin n → ℝ)
    (ha : ∀ i j, a i j = a j i) (hm : ∀ i j, m i j = m j i) :
    (∑ j : Fin n, ∑ i : Fin n, if i < j then
        (a i i * m j j + m i i * a j j - 2 * a i j * m i j) else 0)
      = (∑ i : Fin n, a i i) * (∑ i : Fin n, m i i)
        - ∑ i : Fin n, ∑ j : Fin n, a i j * m i j := by
  have hS := two_mul_sum_lt_sq
      (B := fun i j : Fin n => a i i * m j j + m i i * a j j) (by intro i j; ring)
  have hQ := two_mul_sum_lt_sq
      (B := fun i j : Fin n => a i j * m i j) (by intro i j; rw [ha i j, hm i j])
  have hsplit : (∑ j : Fin n, ∑ i : Fin n, if i < j then
        (a i i * m j j + m i i * a j j - 2 * a i j * m i j) else 0)
      = (∑ j : Fin n, ∑ i : Fin n, if i < j then
          (a i i * m j j + m i i * a j j) else 0)
        - 2 * (∑ j : Fin n, ∑ i : Fin n, if i < j then a i j * m i j else 0) := by
    have hpt : ∀ i j : Fin n, (if i < j then
          (a i i * m j j + m i i * a j j - 2 * a i j * m i j) else 0)
        = (if i < j then (a i i * m j j + m i i * a j j) else 0)
          - 2 * (if i < j then a i j * m i j else 0) := by
      intro i j; by_cases h : i < j <;> simp [h]; ring
    have h1 : (∑ j : Fin n, ∑ i : Fin n, if i < j then
          (a i i * m j j + m i i * a j j - 2 * a i j * m i j) else 0)
        = ∑ j : Fin n, ∑ i : Fin n,
            ((if i < j then (a i i * m j j + m i i * a j j) else 0)
              - 2 * (if i < j then a i j * m i j else 0)) := by
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _
      exact hpt i j
    rw [h1]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  have hSsum : (∑ i : Fin n, ∑ j : Fin n, (a i i * m j j + m i i * a j j))
      = 2 * ((∑ i : Fin n, a i i) * (∑ i : Fin n, m i i)) := by
    calc (∑ i : Fin n, ∑ j : Fin n, (a i i * m j j + m i i * a j j))
        = ∑ i : Fin n, ((∑ j : Fin n, a i i * m j j) + (∑ j : Fin n, m i i * a j j)) := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, ∑ j : Fin n, a i i * m j j)
            + (∑ i : Fin n, ∑ j : Fin n, m i i * a j j) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, a i i) * (∑ j : Fin n, m j j)
            + (∑ i : Fin n, m i i) * (∑ j : Fin n, a j j) := by
          rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum]
      _ = 2 * ((∑ i : Fin n, a i i) * (∑ i : Fin n, m i i)) := by ring
  have hSdiag : (∑ i : Fin n, (a i i * m i i + m i i * a i i))
      = 2 * (∑ i : Fin n, a i i * m i i) := by
    have hcomm : (∑ i : Fin n, m i i * a i i) = (∑ i : Fin n, a i i * m i i) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [Finset.sum_add_distrib, hcomm]; ring
  linarith [hS, hQ, hSsum, hSdiag, hsplit]

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem coord_minor_mixed_eq_trace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : OrthonormalBasis (Fin 4) ℝ E) {A M : E →L[ℝ] E}
    (hA : A.IsSymmetric) (hM : M.IsSymmetric) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪A (b i), b i⟫ * ⟪M (b j), b j⟫ + ⟪M (b i), b i⟫ * ⟪A (b j), b j⟫
          - 2 * ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫) else 0)
      = LinearMap.trace ℝ E ((LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • (1 : E →ₗ[ℝ] E) - (A : E →ₗ[ℝ] E))
          ∘ₗ (M : E →ₗ[ℝ] E)) := by
  classical
  -- Symmetry of the two coordinate matrices.
  have ha : ∀ i j : Fin 4, ⟪A (b i), b j⟫ = ⟪A (b j), b i⟫ := by
    intro i j; rw [hA.apply_clm, real_inner_comm]
  have hm : ∀ i j : Fin 4, ⟪M (b i), b j⟫ = ⟪M (b j), b i⟫ := by
    intro i j; rw [hM.apply_clm, real_inner_comm]
  -- The combinatorial identity for the two coordinate matrices.
  have hkey : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪A (b i), b i⟫ * ⟪M (b j), b j⟫ + ⟪M (b i), b i⟫ * ⟪A (b j), b j⟫
          - 2 * ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫) else 0)
      = (∑ i : Fin 4, ⟪A (b i), b i⟫) * (∑ i : Fin 4, ⟪M (b i), b i⟫)
        - ∑ i : Fin 4, ∑ j : Fin 4, ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫ :=
    pair_mixed_eq (a := fun i j => ⟪A (b i), b j⟫) (m := fun i j => ⟪M (b i), b j⟫) ha hm
  -- Traces in the orthonormal basis.
  have htrA : (∑ i : Fin 4, ⟪A (b i), b i⟫) = LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) := by
    rw [LinearMap.trace_eq_sum_inner (A : E →ₗ[ℝ] E) b]
    apply Finset.sum_congr rfl; intro i _
    exact real_inner_comm _ _
  have htrM : (∑ i : Fin 4, ⟪M (b i), b i⟫) = LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) := by
    rw [LinearMap.trace_eq_sum_inner (M : E →ₗ[ℝ] E) b]
    apply Finset.sum_congr rfl; intro i _
    exact real_inner_comm _ _
  have htrAM : (∑ i : Fin 4, ∑ j : Fin 4, ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫)
      = LinearMap.trace ℝ E ((A : E →ₗ[ℝ] E) ∘ₗ (M : E →ₗ[ℝ] E)) := by
    rw [Commons.Analysis.InnerProductSpace.trace_comp_eq_sum_inner_coord b A M]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hm i j]
  -- Linearity of the trace in the right-hand side.
  have hRHS : LinearMap.trace ℝ E
        ((LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • (1 : E →ₗ[ℝ] E)
          - (A : E →ₗ[ℝ] E)) ∘ₗ (M : E →ₗ[ℝ] E))
      = LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) * LinearMap.trace ℝ E (M : E →ₗ[ℝ] E)
        - LinearMap.trace ℝ E ((A : E →ₗ[ℝ] E) ∘ₗ (M : E →ₗ[ℝ] E)) := by
    have hcomp : ((LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • (1 : E →ₗ[ℝ] E)
          - (A : E →ₗ[ℝ] E)) ∘ₗ (M : E →ₗ[ℝ] E))
        = (LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • (M : E →ₗ[ℝ] E))
          - (A : E →ₗ[ℝ] E) ∘ₗ (M : E →ₗ[ℝ] E) := by
      ext x
      simp
    rw [hcomp, map_sub, map_smul, smul_eq_mul]
  rw [hkey, htrA, htrM, htrAM, hRHS]

end Commons.Analysis.Sigma2
