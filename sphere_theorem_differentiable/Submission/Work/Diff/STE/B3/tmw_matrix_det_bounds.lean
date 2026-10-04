import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open Matrix

/-!
# Uniform determinant bounds for matrices with a two-sided quadratic-form bound

If `A` is a real symmetric `n × n` matrix whose quadratic form satisfies
`mlo * ∑ ξᵢ² ≤ ∑ A p q ξ p ξ q ≤ Mhi * ∑ ξᵢ²` for all `ξ`, with `mlo > 0`, then `det A` is
trapped between two positive constants depending only on `n`, `mlo`, `Mhi`.  Concretely
`mlo ^ n ≤ det A ≤ Mhi ^ n`: the quadratic-form bounds say that every eigenvalue of `A` lies in
`[mlo, Mhi]` (each eigenvalue is evaluated on its own unit eigenvector), and the determinant is the
product of the eigenvalues.

The eigenvalue bound is obtained from the spectral theory of Hermitian matrices
(`Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.mulVec_eigenvectorBasis`,
`Matrix.IsHermitian.det_eq_prod_eigenvalues`); no completeness or compactness argument is needed.
-/

/-- The quadratic form of a real matrix, written as a `dotProduct`. -/
private lemma dotProduct_mulVec_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    star ξ ⬝ᵥ (M *ᵥ ξ) = ∑ p, ∑ q, M p q * ξ p * ξ q := by
  simp only [dotProduct, mulVec, Finset.mul_sum, star_trivial]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- A vector of an orthonormal basis has `∑ ξᵢ² = 1 > 0`. -/
private lemma eigenvector_sum_sq_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (i : Fin n) : 0 < ∑ j, (hM.eigenvectorBasis i).ofLp j ^ 2 := by
  have h0 := EuclideanSpace.inner_eq_star_dotProduct (hM.eigenvectorBasis i) (hM.eigenvectorBasis i)
  rw [inner_self_eq_norm_sq_to_K, hM.eigenvectorBasis.orthonormal.1 i] at h0
  have h1 : (1 : ℝ) = ∑ j, (hM.eigenvectorBasis i).ofLp j * (hM.eigenvectorBasis i).ofLp j := by
    simpa [dotProduct] using h0
  rw [show ∑ j, (hM.eigenvectorBasis i).ofLp j ^ 2
        = ∑ j, (hM.eigenvectorBasis i).ofLp j * (hM.eigenvectorBasis i).ofLp j from
      Finset.sum_congr rfl (fun j _ => by ring)]
  rw [← h1]
  norm_num

/-- Every eigenvalue of a symmetric matrix obeying the two-sided quadratic-form bound lies in
`[mlo, Mhi]`. -/
private lemma eigenvalue_mem_Icc {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {mlo Mhi : ℝ}
    (hM : M.IsHermitian)
    (hlow : ∀ ξ : Fin n → ℝ, mlo * ∑ i, ξ i ^ 2 ≤ ∑ p, ∑ q, M p q * ξ p * ξ q)
    (hup : ∀ ξ : Fin n → ℝ, (∑ p, ∑ q, M p q * ξ p * ξ q) ≤ Mhi * ∑ i, ξ i ^ 2)
    (i : Fin n) : mlo ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ Mhi := by
  set ξ : Fin n → ℝ := (hM.eigenvectorBasis i).ofLp with hξ
  set S : ℝ := ∑ j, (ξ j) ^ 2 with hSdef
  have hSpos : 0 < S := by
    rw [hSdef, hξ]
    exact eigenvector_sum_sq_pos hM i
  have hmv : M *ᵥ ξ = (hM.eigenvalues i) • ξ := by
    rw [hξ]
    exact hM.mulVec_eigenvectorBasis i
  have hQS : ∑ p, ∑ q, M p q * ξ p * ξ q = (hM.eigenvalues i) * S := by
    rw [← dotProduct_mulVec_eq_sum M ξ, hmv, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [dotProduct, star_trivial]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  constructor
  · refine le_of_mul_le_mul_right ?_ hSpos
    have h := hlow ξ
    rw [← hSdef] at h
    rwa [hQS] at h
  · refine le_of_mul_le_mul_right ?_ hSpos
    have h := hup ξ
    rw [← hSdef] at h
    rwa [hQS] at h

/-- The determinant of a symmetric matrix obeying the two-sided quadratic-form bound is itself
bounded by the `n`-th powers of the two constants. -/
private lemma det_bounds_of_quadForm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {mlo Mhi : ℝ}
    (hmlo : 0 < mlo) (hM : M.IsHermitian)
    (hlow : ∀ ξ : Fin n → ℝ, mlo * ∑ i, ξ i ^ 2 ≤ ∑ p, ∑ q, M p q * ξ p * ξ q)
    (hup : ∀ ξ : Fin n → ℝ, (∑ p, ∑ q, M p q * ξ p * ξ q) ≤ Mhi * ∑ i, ξ i ^ 2) :
    mlo ^ n ≤ M.det ∧ M.det ≤ Mhi ^ n := by
  have hb : ∀ i, mlo ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ Mhi :=
    fun i => eigenvalue_mem_Icc hM hlow hup i
  have hdet : M.det = ∏ i, hM.eigenvalues i := by simpa using hM.det_eq_prod_eigenvalues
  constructor
  · rw [hdet]
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin n => mlo)
      (g := fun i => hM.eigenvalues i) (fun _ _ => le_of_lt hmlo) (fun i _ => (hb i).1)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  · rw [hdet]
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun i => hM.eigenvalues i)
      (g := fun _ : Fin n => Mhi) (fun i _ => le_trans (le_of_lt hmlo) (hb i).1)
      (fun i _ => (hb i).2)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h

theorem tmw_matrix_det_bounds (n : ℕ) (mlo Mhi : ℝ) (hmlo : 0 < mlo) :
    ∃ (cl ch : ℝ), 0 < cl ∧ cl < ch ∧
      ∀ A : Fin n → Fin n → ℝ,
        (∀ i j, A i j = A j i) →
        (∀ ξ : Fin n → ℝ, mlo * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A p q * ξ p * ξ q) →
        (∀ ξ : Fin n → ℝ, (∑ p, ∑ q, A p q * ξ p * ξ q) ≤ Mhi * ∑ i, (ξ i) ^ 2) →
        cl ≤ (Matrix.of A).det ∧ (Matrix.of A).det ≤ ch := by
  refine ⟨min 1 (mlo ^ n) / 2, 2 * max 1 (Mhi ^ n), ?_, ?_, ?_⟩
  · have h1 : 0 < min 1 (mlo ^ n) := lt_min one_pos (pow_pos hmlo n)
    linarith
  · have h1 : min 1 (mlo ^ n) / 2 ≤ 1 / 2 := by
      have h2 : 0 < min 1 (mlo ^ n) := lt_min one_pos (pow_pos hmlo n)
      have h3 := min_le_left (1 : ℝ) (mlo ^ n)
      linarith
    have h2 : (1 : ℝ) ≤ 2 * max 1 (Mhi ^ n) := by
      have h3 := le_max_left (1 : ℝ) (Mhi ^ n)
      linarith
    linarith
  · intro A hsym hlow hup
    have hM : (Matrix.of A).IsHermitian :=
      Matrix.IsHermitian.ext (fun i j => by simpa using hsym j i)
    have hlow' : ∀ ξ : Fin n → ℝ,
        mlo * ∑ i, ξ i ^ 2 ≤ ∑ p, ∑ q, (Matrix.of A) p q * ξ p * ξ q := by
      intro ξ
      simpa using hlow ξ
    have hup' : ∀ ξ : Fin n → ℝ,
        (∑ p, ∑ q, (Matrix.of A) p q * ξ p * ξ q) ≤ Mhi * ∑ i, ξ i ^ 2 := by
      intro ξ
      simpa using hup ξ
    obtain ⟨ha, hb⟩ := det_bounds_of_quadForm hmlo hM hlow' hup'
    constructor
    · have h3 : min 1 (mlo ^ n) / 2 ≤ mlo ^ n := by
        have h4 : 0 < min 1 (mlo ^ n) := lt_min one_pos (pow_pos hmlo n)
        have h5 := min_le_right (1 : ℝ) (mlo ^ n)
        linarith
      linarith
    · have h3 : Mhi ^ n ≤ 2 * max 1 (Mhi ^ n) := by
        have h4 := le_max_right (1 : ℝ) (Mhi ^ n)
        have h5 := le_max_left (1 : ℝ) (Mhi ^ n)
        linarith
      linarith

end Work.Diff.STE.B3
