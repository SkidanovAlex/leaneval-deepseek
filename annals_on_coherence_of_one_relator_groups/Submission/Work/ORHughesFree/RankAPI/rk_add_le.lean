import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.RankAPI

open Work.ORHughesFree

/-- `A + B` is obtained from the block diagonal matrix `diag(A, B)` by multiplying on the left by
the row `[1, 1]` and on the right by the column `[1; 1]`. -/
private lemma add_eq_sandwich {R : Type*} [Ring R] {n m : ℕ}
    (A B : Matrix (Fin n) (Fin m) R) :
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix
        id finSumFinEquiv.symm
      * blockDiagFin A B
      * (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin m) (Fin m) R)).submatrix
        finSumFinEquiv.symm id
    = A + B := by
  have h1 : (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix
        id finSumFinEquiv.symm
      * blockDiagFin A B
      = (Matrix.fromCols A B).submatrix id finSumFinEquiv.symm := by
    rw [blockDiagFin, Matrix.submatrix_mul_equiv]
    simp [Matrix.fromCols_mul_fromBlocks]
  rw [h1, Matrix.submatrix_mul_equiv]
  simp [Matrix.fromCols_mul_fromRows]

theorem rk_add_le {R : Type*} [Ring R] (rk : SylvesterRank R) {n m : ℕ}
    (A B : Matrix (Fin n) (Fin m) R) :
    rk.rk n m (A + B) ≤ rk.rk n m A + rk.rk n m B := by
  set P : Matrix (Fin n) (Fin (n + n)) R :=
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix
      id finSumFinEquiv.symm with hP
  set Q : Matrix (Fin (m + m)) (Fin m) R :=
    (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin m) (Fin m) R)).submatrix
      finSumFinEquiv.symm id with hQ
  have hPQ : P * blockDiagFin A B * Q = A + B := by
    rw [hP, hQ]
    exact add_eq_sandwich A B
  rw [← hPQ]
  calc rk.rk n m (P * blockDiagFin A B * Q)
      ≤ rk.rk n (m + m) (P * blockDiagFin A B) :=
        rk.rk_mul_le_left (P * blockDiagFin A B) Q
    _ ≤ rk.rk (n + n) (m + m) (blockDiagFin A B) :=
        rk.rk_mul_le_right P (blockDiagFin A B)
    _ = rk.rk n m A + rk.rk n m B := rk.rk_blockDiag A B

end Work.ORHughesFree.RankAPI
