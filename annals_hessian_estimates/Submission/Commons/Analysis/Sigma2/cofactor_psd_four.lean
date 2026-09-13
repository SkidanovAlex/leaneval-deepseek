import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply

namespace Commons.Analysis.Sigma2

/- If `T` is a symmetric endomorphism of a finite-dimensional real inner product space, all of
whose eigenvalues (as enumerated by `hT.eigenvalues hn`) are `≤ c`, then the quadratic form of
`c • 1 - T` is nonnegative, i.e. `c • 1 - T` is positive semidefinite.  The proof diagonalises `T`
in its orthonormal eigenbasis `b = hT.eigenvectorBasis hn`: writing `v = ∑ i, ⟪b i, v⟫ • b i`
gives `⟪T v, v⟫ = ∑ i, λ i * ⟪b i, v⟫ ^ 2` and `⟪v, v⟫ = ∑ i, ⟪b i, v⟫ ^ 2`, whence
`⟪(c • 1 - T) v, v⟫ = ∑ i, (c - λ i) * ⟪b i, v⟫ ^ 2 ≥ 0`. -/
open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem quadform_nonneg_of_eigen_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (c : ℝ)
    (h : ∀ i : Fin n, hT.eigenvalues hn i ≤ c) :
    ∀ v : E, 0 ≤ ⟪(c • (1 : E →L[ℝ] E) - T) v, v⟫ := by
  intro v
  let b := hT.eigenvectorBasis hn
  have hsym : ∀ i : Fin n, ⟪T v, b i⟫ = hT.eigenvalues hn i * ⟪b i, v⟫ := by
    intro i
    show ⟪(T : E →ₗ[ℝ] E) v, b i⟫ = hT.eigenvalues hn i * ⟪b i, v⟫
    rw [hT v (b i), hT.apply_eigenvectorBasis hn i, real_inner_smul_right, real_inner_comm]
    simp [b]
  have hTv : ⟪T v, v⟫ = ∑ i, hT.eigenvalues hn i * (⟪b i, v⟫)^2 := by
    rw [← b.sum_inner_mul_inner (T v) v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym i]
    ring
  have hvv : ⟪v, v⟫ = ∑ i, (⟪b i, v⟫)^2 := by
    rw [← b.sum_inner_mul_inner v v]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]
    ring
  have hgoal : ⟪(c • (1 : E →L[ℝ] E) - T) v, v⟫
      = ∑ i, (c - hT.eigenvalues hn i) * (⟪b i, v⟫)^2 := by
    rw [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, real_inner_smul_left]
    rw [hvv, hTv, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hgoal]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · linarith [h i]
  · positivity

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem cofactor_psd_four {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = 4)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4,
        if i < j then hT.eigenvalues hn i * hT.eigenvalues hn j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, hT.eigenvalues hn i) :
    ∀ v : E, 0 ≤ ⟪((∑ i : Fin 4, hT.eigenvalues hn i) • (1 : E →L[ℝ] E) - T) v, v⟫ := by
  intro v
  -- `hT.eigenvalues hn` is listed in decreasing order, hence satisfies the monotonicity
  -- hypothesis of `linearized_pos_four`.
  have hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → hT.eigenvalues hn j ≤ hT.eigenvalues hn i :=
    hT.eigenvalues_antitone hn
  -- The algebraic core: `σ₁ - λ i > 0` for every eigenvalue, i.e. `λ i ≤ σ₁`.
  have hpos := linearized_pos_four (hT.eigenvalues hn) hmono hσ2 hσ1
  have hle : ∀ i : Fin 4, hT.eigenvalues hn i ≤ ∑ j : Fin 4, hT.eigenvalues hn j := by
    intro i
    have := hpos i
    linarith
  -- Diagonalize in the orthonormal eigenbasis.
  exact quadform_nonneg_of_eigen_le hT 4 hn (∑ j : Fin 4, hT.eigenvalues hn j) hle v

end Commons.Analysis.Sigma2