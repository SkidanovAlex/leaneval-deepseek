import Mathlib
import Submission.Work.KT.Psi.Basic

namespace Work.KT.Psi

/-!
# `Work.KT.Psi.kronMat_swap_comm`

The Kronecker square `P ⊗ P` commutes with the swap operator on the tensor product
`Fin n × Fin n`, i.e. it commutes with the permutation matrix of `swapPerm n`.

This is used to control the interaction of the symmetric/antisymmetric projectors
`(1 ± swap)/2` with a factor `p ⊗ p` in `K₀`.

The proof is a direct entrywise computation on the product index type `Fin n × Fin n`,
transported to `Fin (n * n)` along `finProdFinEquiv` by functoriality of `Matrix.reindex`.
The only place where the commutativity hypothesis `hA` is used is the comparison of the
two entries `P i l * P j k` and `P j k * P i l`.
-/

open Matrix

/-- Left multiplication by the permutation matrix of `σ` reindexes the rows by `σ`. -/
theorem permMatrix_mul_submatrix {A : Type} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (X : Matrix ι ι A) : σ.permMatrix A * X = X.submatrix σ id := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (σ i)]
  · rw [Work.KT.permMatrix_apply' σ i (σ i), if_pos rfl, one_mul]
  · intro b _ hb
    rw [Work.KT.permMatrix_apply' σ i b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Right multiplication by the permutation matrix of `σ` reindexes the columns by `σ⁻¹`. -/
theorem mul_permMatrix_submatrix {A : Type} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (X : Matrix ι ι A) : X * σ.permMatrix A = X.submatrix id σ.symm := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [Work.KT.permMatrix_apply' σ (σ.symm j) j, Equiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro b _ hb
    have h : ¬ (σ b = j) := fun hh => hb ((Equiv.eq_symm_apply σ).mpr hh)
    rw [Work.KT.permMatrix_apply' σ b j, if_neg h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- On the product index type, `P ⊗ P` commutes with the swap of the two factors. -/
theorem kroneckerMap_self_comm_prodComm {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x)
    {n : ℕ} (P : Matrix (Fin n) (Fin n) A) :
    Matrix.kroneckerMap (· * ·) P P * Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))
      = Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)) *
          Matrix.kroneckerMap (· * ·) P P := by
  rw [mul_permMatrix_submatrix, permMatrix_mul_submatrix, Equiv.prodComm_symm]
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, id_eq, Equiv.prodComm_apply,
    Prod.swap_prod_mk]
  exact hA _ _

theorem kronMat_swap_comm {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x)
    {n : ℕ} (P : Matrix (Fin n) (Fin n) A) :
    kronMat P P * (swapPerm n).permMatrix A = (swapPerm n).permMatrix A * kronMat P P := by
  let e : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv
  let K : Matrix (Fin n × Fin n) (Fin n × Fin n) A := Matrix.kroneckerMap (· * ·) P P
  let S : Matrix (Fin n × Fin n) (Fin n × Fin n) A :=
    Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))
  have hswap : e.symm.trans ((Equiv.prodComm (Fin n) (Fin n)).trans e) = swapPerm n := by
    rw [← Equiv.trans_assoc]
    rfl
  have hK : kronMat P P = Matrix.reindex e e K := rfl
  have hS : (swapPerm n).permMatrix A = Matrix.reindex e e S := by
    rw [← hswap]
    rw [← Work.KT.reindex_permMatrix e (Equiv.prodComm (Fin n) (Fin n))]
  have hKS : K * S = S * K := kroneckerMap_self_comm_prodComm hA P
  calc kronMat P P * (swapPerm n).permMatrix A
      = Matrix.reindex e e K * Matrix.reindex e e S := by rw [hK, hS]
    _ = Matrix.reindex e e (K * S) := (map_mul (Matrix.reindexRingEquiv A e) K S).symm
    _ = Matrix.reindex e e (S * K) := by rw [hKS]
    _ = Matrix.reindex e e S * Matrix.reindex e e K := map_mul (Matrix.reindexRingEquiv A e) S K
    _ = (swapPerm n).permMatrix A * kronMat P P := by rw [hK, hS]

end Work.KT.Psi
