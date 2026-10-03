import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.RankAPI

open Matrix

/-- A Sylvester rank function assigns to the `n × n` identity matrix the value `n`.

This is the formal counterpart of the fact (immediate from (SMat1) and (SMat3)
combined with the observation that the identity of size `n + 1` is
`blockDiag 1_n 1_1`) that a Sylvester matrix rank function is normalized on
identities. -/
private theorem rk_one_fin_aux {R : Type*} [Ring R] (rk : SylvesterRank R) (n : ℕ) :
    rk.rk n n (1 : Matrix (Fin n) (Fin n) R) = n := by
  induction n with
  | zero =>
    rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) R) 0, rk.rk_zero]
    norm_num
  | succ n ih =>
    -- `1_{n+1} = blockDiag 1_n 1_1`, so (SMat3) applies.
    have h : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        blockDiagFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin 1) (Fin 1) R) := by
      rw [blockDiagFin, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
    rw [h, rk.rk_blockDiag, ih, rk.rk_one]
    norm_num

/-- The rank of a matrix is at most its number of columns.

Indeed `A = A * 1_m`, so (SMat2) gives `rk A ≤ rk 1_m = m`. -/
theorem rk_le_right {R : Type*} [Ring R] (rk : SylvesterRank R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : rk.rk n m A ≤ m := by
  rw [← Matrix.mul_one A]
  calc rk.rk n m (A * 1) ≤ rk.rk m m (1 : Matrix (Fin m) (Fin m) R) := rk.rk_mul_le_right A 1
    _ = (m : ℝ) := rk_one_fin_aux rk m

end Work.ORHughesFree.RankAPI
