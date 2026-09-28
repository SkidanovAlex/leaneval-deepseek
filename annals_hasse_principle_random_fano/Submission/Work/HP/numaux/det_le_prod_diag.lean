import Mathlib

namespace Work.HP.numaux

open Matrix in
/-- Every positive semidefinite real matrix admits an "orthogonal diagonalization" in the form
needed here: unit-norm rows and columns of an orthogonal matrix `U` together with nonnegative
`lam` such that the diagonal entries of `A` are the convex combinations `∑ k, U i k * U i k * lam k`
and `A.det = ∏ k, lam k`. -/
theorem exists_orthogonal_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) :
    ∃ (U : Matrix n n ℝ) (lam : n → ℝ),
      (∀ i, ∑ k, U i k * U i k = 1) ∧
      (∀ k, ∑ i, U i k * U i k = 1) ∧
      (∀ k, 0 ≤ lam k) ∧
      (∀ i, A i i = ∑ k, U i k * U i k * lam k) ∧
      A.det = ∏ k, lam k := by
  refine ⟨(hA.1.eigenvectorUnitary : Matrix n n ℝ), hA.1.eigenvalues, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h : ((hA.1.eigenvectorUnitary : Matrix n n ℝ) *
        star (hA.1.eigenvectorUnitary : Matrix n n ℝ)) i i = (1 : Matrix n n ℝ) i i := by
      rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  · intro k
    have h : (star (hA.1.eigenvectorUnitary : Matrix n n ℝ) *
        (hA.1.eigenvectorUnitary : Matrix n n ℝ)) k k = (1 : Matrix n n ℝ) k k := by
      rw [Unitary.coe_star_mul_self]
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  · intro k
    exact hA.eigenvalues_nonneg k
  · intro i
    conv_lhs => rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, star_trivial,
      Function.comp_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single x]
    · simp
      ring
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  · rw [hA.1.det_eq_prod_eigenvalues]
    exact Finset.prod_congr rfl fun i _ => rfl

/-- Weighted-AMGM form of the "doubly stochastic" product inequality:
if `c` is a nonnegative matrix whose rows and columns each sum to `1`, then for any
nonnegative `lam` the product of the `lam k` is at most the product over rows `i` of the
convex combinations `∑ k, c i k * lam k`. -/
theorem prod_le_prod_of_doubly_stochastic {n : Type*} [Fintype n] [DecidableEq n]
    {c : n → n → ℝ} {lam : n → ℝ}
    (hc : ∀ i k, 0 ≤ c i k) (hrow : ∀ i, ∑ k, c i k = 1) (hcol : ∀ k, ∑ i, c i k = 1)
    (hlam : ∀ k, 0 ≤ lam k) :
    ∏ k, lam k ≤ ∏ i, ∑ k, c i k * lam k := by
  have h1 : ∀ i, ∏ k, (lam k) ^ (c i k) ≤ ∑ k, c i k * lam k := by
    intro i
    have := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset n) (fun k => c i k)
      (fun k => lam k) (fun k _ => hc i k) (by simpa using hrow i) (fun k _ => hlam k)
    simpa using this
  have key : ∏ k, lam k = ∏ i, ∏ k, (lam k) ^ (c i k) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro k _
    rw [← Real.rpow_sum_of_nonneg (hlam k) (fun i _ => hc i k), hcol k, Real.rpow_one]
  rw [key]
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (hlam k) _)
  · intro i _
    exact h1 i

theorem det_le_prod_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i := by
  obtain ⟨U, lam, hrow, hcol, hlam, hdiag, hdet⟩ := exists_orthogonal_diag hA
  rw [hdet]
  calc ∏ k, lam k ≤ ∏ i, ∑ k, U i k * U i k * lam k :=
        prod_le_prod_of_doubly_stochastic (fun i k => mul_self_nonneg (U i k)) hrow hcol hlam
    _ = ∏ i, A i i := Finset.prod_congr rfl fun i _ => (hdiag i).symm

end Work.HP.numaux
