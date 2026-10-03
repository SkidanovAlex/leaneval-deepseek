/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance of the Sylvester rank under reindexing

For a Sylvester matrix rank function `rk` on a ring `R` and an invertible change of the index
sets, `rk` does not change: the reindexed matrix `Matrix.reindex e f A` has the same rank as `A`.

The proof writes `Matrix.reindex e f A` as a product `P * A * Q` of `A` with two
"permutation-type" matrices, i.e. submatrices of identity matrices; each of them admits a
one-sided inverse, so the rank is unchanged by `SylvesterRank.rk_eq_of_left_inverse_mul` and
`SylvesterRank.rk_eq_of_mul_right_inverse`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.RankAPI

open Matrix

/-- Reindexing a matrix is the same as multiplying it by the two permutation-type matrices
`(1 : Matrix (Fin n) (Fin n) R).submatrix e.symm id` (on the left) and
`(1 : Matrix (Fin m) (Fin m) R).submatrix id f.symm` (on the right). -/
private lemma reindex_eq_mul {R : Type*} [Ring R] {n n' m m' : ℕ} (e : Fin n ≃ Fin n')
    (f : Fin m ≃ Fin m') (A : Matrix (Fin n) (Fin m) R) :
    Matrix.reindex e f A = ((1 : Matrix (Fin n) (Fin n) R).submatrix e.symm id) * A
      * ((1 : Matrix (Fin m) (Fin m) R).submatrix id f.symm) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]

/-- The permutation-type matrix `(1 : Matrix (Fin n) (Fin n) R).submatrix e.symm id` has
`(1 : Matrix (Fin n') (Fin n') R).submatrix e id` as a left inverse. -/
private lemma submatrix_one_mul_submatrix_symm_one {R : Type*} [Ring R] {n n' : ℕ}
    (e : Fin n ≃ Fin n') :
    ((1 : Matrix (Fin n') (Fin n') R).submatrix e id)
      * ((1 : Matrix (Fin n) (Fin n) R).submatrix e.symm id) = 1 := by
  rw [Matrix.mul_submatrix_one (e₁ := e.symm) (e₂ := (id : Fin n → Fin n))
    (M := (1 : Matrix (Fin n') (Fin n') R).submatrix e id)]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

/-- The permutation-type matrix `(1 : Matrix (Fin m) (Fin m) R).submatrix id f.symm` has
`(1 : Matrix (Fin m) (Fin m) R).submatrix f.symm id` as a right inverse. -/
private lemma submatrix_symm_one_mul_submatrix_one {R : Type*} [Ring R] {m m' : ℕ}
    (f : Fin m ≃ Fin m') :
    ((1 : Matrix (Fin m) (Fin m) R).submatrix id f.symm)
      * ((1 : Matrix (Fin m) (Fin m) R).submatrix f.symm id) = 1 := by
  simp

theorem rk_reindex {R : Type*} [Ring R] (rk : SylvesterRank R) {n n' m m' : ℕ}
    (e : Fin n ≃ Fin n') (f : Fin m ≃ Fin m') (A : Matrix (Fin n) (Fin m) R) :
    rk.rk n' m' (Matrix.reindex e f A) = rk.rk n m A := by
  set P : Matrix (Fin n') (Fin n) R := (1 : Matrix (Fin n) (Fin n) R).submatrix e.symm id with hP
  set P' : Matrix (Fin n) (Fin n') R := (1 : Matrix (Fin n') (Fin n') R).submatrix e id with hP'
  set Q : Matrix (Fin m) (Fin m') R := (1 : Matrix (Fin m) (Fin m) R).submatrix id f.symm with hQ
  set Q' : Matrix (Fin m') (Fin m) R := (1 : Matrix (Fin m) (Fin m) R).submatrix f.symm id with hQ'
  have hA : Matrix.reindex e f A = P * A * Q := by
    rw [hP, hQ]
    exact reindex_eq_mul e f A
  have hPP' : P' * P = 1 := by
    rw [hP', hP]
    exact submatrix_one_mul_submatrix_symm_one e
  have hQQ' : Q * Q' = 1 := by
    rw [hQ, hQ']
    exact submatrix_symm_one_mul_submatrix_one f
  have h2 : rk.rk n' m' (P * A * Q) = rk.rk n' m (P * A) :=
    SylvesterRank.rk_eq_of_mul_right_inverse rk (P * A) Q Q' hQQ'
  have h3 : rk.rk n' m (P * A) = rk.rk n m A :=
    SylvesterRank.rk_eq_of_left_inverse_mul rk P P' hPP' A
  rw [hA, h2, h3]

end Work.ORHughesFree.RankAPI
