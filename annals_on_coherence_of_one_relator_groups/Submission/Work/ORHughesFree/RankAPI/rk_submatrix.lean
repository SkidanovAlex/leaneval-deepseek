import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.RankAPI

open Matrix

variable {R : Type*} [Ring R]

/-- The `n' × n` matrix with a `1` in position `(i, e i)`: left multiplication of a
matrix by `rowSel e` selects the rows indexed by `e`. -/
def rowSel {n n' : ℕ} (e : Fin n' → Fin n) : Matrix (Fin n') (Fin n) R :=
  fun i j => if e i = j then 1 else 0

/-- The `m × m'` matrix with a `1` in position `(f j, j)`: right multiplication of a
matrix by `colSel f` selects the columns indexed by `f`. -/
def colSel {m m' : ℕ} (f : Fin m' → Fin m) : Matrix (Fin m) (Fin m') R :=
  fun k j => if k = f j then 1 else 0

theorem rowSel_mul {n n' m : ℕ} (e : Fin n' → Fin n) (A : Matrix (Fin n) (Fin m) R) :
    rowSel (R := R) e * A = A.submatrix e id := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, rowSel, id_eq]
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    rw [if_neg (fun h : e i = j => hj h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (e i)) h

theorem submatrix_mul_colSel {n n' m m' : ℕ} (e : Fin n' → Fin n) (f : Fin m' → Fin m)
    (A : Matrix (Fin n) (Fin m) R) :
    A.submatrix e id * colSel (R := R) f = A.submatrix e f := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, colSel, id_eq]
  rw [Finset.sum_eq_single (f j)]
  · simp
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (f j)) h

/-- A submatrix is a product of the original matrix with explicit row- and
column-selecting matrices. -/
theorem submatrix_eq_mul {n n' m m' : ℕ} (e : Fin n' → Fin n) (f : Fin m' → Fin m)
    (A : Matrix (Fin n) (Fin m) R) :
    A.submatrix e f = rowSel (R := R) e * (A * colSel (R := R) f) := by
  rw [← Matrix.mul_assoc, rowSel_mul, submatrix_mul_colSel]

/-- For a Sylvester rank function, the rank of a matrix does not increase when passing
to a submatrix, even when the index maps are not injective. -/
theorem rk_submatrix {R : Type*} [Ring R] (rk : SylvesterRank R) {n n' m m' : ℕ}
    (e : Fin n' → Fin n) (f : Fin m' → Fin m) (A : Matrix (Fin n) (Fin m) R) :
    rk.rk n' m' (A.submatrix e f) ≤ rk.rk n m A := by
  rw [submatrix_eq_mul e f A]
  exact le_trans (rk.rk_mul_le_right (rowSel (R := R) e) (A * colSel (R := R) f))
    (rk.rk_mul_le_left A (colSel (R := R) f))

end Work.ORHughesFree.RankAPI
