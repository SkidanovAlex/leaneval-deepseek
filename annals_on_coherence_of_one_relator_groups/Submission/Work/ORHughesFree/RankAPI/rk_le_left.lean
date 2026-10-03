import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.RankAPI

open Matrix

/-- The rank of the `n × n` identity matrix is `n`.

This follows by induction from the block-diagonal axiom `(SMat3)`: the identity on
`Fin (n+1)` is, up to the standard reindexing, the block diagonal of the identity on `Fin n`
and the `1 × 1` identity, whose rank is `1` by `(SMat1)`. -/
theorem rk_identity_eq {R : Type*} [Ring R] (rk : SylvesterRank R) (n : ℕ) :
    rk.rk n n (1 : Matrix (Fin n) (Fin n) R) = n := by
  induction n with
  | zero =>
    rw [show (1 : Matrix (Fin 0) (Fin 0) R) = 0 from Subsingleton.elim _ _]
    rw [rk.rk_zero]
    simp
  | succ n ih =>
    rw [show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
          = blockDiagFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin 1) (Fin 1) R) from by
      simp only [blockDiagFin, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]]
    rw [rk.rk_blockDiag, ih, rk.rk_one]
    push_cast
    ring

/-- A Sylvester rank function assigns to every `n × m` matrix a rank of at most `n`.

Indeed `A = 1 * A`, so `(SMat2)` gives `rk A ≤ rk 1`, and the rank of the `n × n` identity
matrix equals `n`. -/
theorem rk_le_left {R : Type*} [Ring R] (rk : SylvesterRank R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : rk.rk n m A ≤ n := by
  calc rk.rk n m A ≤ rk.rk n n (1 : Matrix (Fin n) (Fin n) R) := by
        have h := rk.rk_mul_le_left (1 : Matrix (Fin n) (Fin n) R) A
        rwa [Matrix.one_mul] at h
    _ = n := rk_identity_eq rk n

end Work.ORHughesFree.RankAPI
