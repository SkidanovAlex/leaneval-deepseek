import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.RankAPI

open Work.ORHughesFree

/-- The `(n+1) × (n+1)` identity matrix, split as the block diagonal of the `n × n` identity
and the `1 × 1` identity. -/
theorem blockDiagFin_one_succ {R : Type*} [Ring R] (n : ℕ) :
    blockDiagFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin 1) (Fin 1) R) = 1 := by
  rw [blockDiagFin, Matrix.fromBlocks_one,
    Matrix.submatrix_one (finSumFinEquiv.symm : Fin (n + 1) → Fin n ⊕ Fin 1) (Equiv.injective _)]

theorem rk_one_fin {R : Type*} [Ring R] (rk : SylvesterRank R) (n : ℕ) :
    rk.rk n n (1 : Matrix (Fin n) (Fin n) R) = n := by
  induction n with
  | zero =>
    have h : (1 : Matrix (Fin 0) (Fin 0) R) = 0 := by
      ext i; exact Fin.elim0 i
    rw [h, rk.rk_zero]
    norm_num
  | succ n ih =>
    have h : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
        = blockDiagFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin 1) (Fin 1) R) :=
      (blockDiagFin_one_succ (R := R) n).symm
    rw [h, rk.rk_blockDiag, ih, rk.rk_one]
    push_cast
    ring

end Work.ORHughesFree.RankAPI
