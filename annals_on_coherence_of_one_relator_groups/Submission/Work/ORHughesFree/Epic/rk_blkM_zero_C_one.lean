import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.BlockLower
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin

namespace Work.ORHughesFree.Epic

open Matrix

/-- Product of two block lower-triangular matrices `[[A,0],[C,B]]` and `[[A',0],[C',B']]`:
the result is again block lower-triangular, with bottom-left block `C * A' + B * C'`.

(This is the specialisation of `Matrix.fromBlocks_multiply` to the shapes normalized by
`blockLowerFin`.) -/
private lemma blockLowerFin_mul_aux {R : Type*} [Ring R] {a b c d f g : ℕ}
    (A : Matrix (Fin a) (Fin c) R) (B : Matrix (Fin b) (Fin d) R)
    (C : Matrix (Fin b) (Fin c) R)
    (A' : Matrix (Fin c) (Fin g) R) (B' : Matrix (Fin d) (Fin f) R)
    (C' : Matrix (Fin d) (Fin g) R) :
    blockLowerFin A B C * blockLowerFin A' B' C'
      = blockLowerFin (A * A') (B * B') (C * A' + B * C') := by
  rw [blockLowerFin, blockLowerFin, blockLowerFin,
    Matrix.submatrix_mul_equiv _ _ _ (finSumFinEquiv.symm) _,
    Matrix.fromBlocks_multiply]
  congr 1
  all_goals simp

/-- The block lower-triangular matrix with identity diagonal blocks and vanishing lower-left
block is the identity. -/
private lemma blockLowerFin_one_aux {R : Type*} [Ring R] (n m : ℕ) :
    blockLowerFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin m) (Fin m) R)
      (0 : Matrix (Fin m) (Fin n) R) = 1 := by
  rw [blockLowerFin, Matrix.fromBlocks_one, Matrix.submatrix_one _ (Equiv.injective _)]

/-- The rank of the block lower-triangular matrix `[[A, 0], [C, 1]]` equals `rk A + n'`.

The matrix `[[A,0],[C,1]]` becomes the block diagonal matrix `diag(A, 1)` after multiplication on
the right by the invertible block lower-triangular matrix `[[1,0],[-C,1]]`; rank is invariant under
right multiplication by a matrix with a right inverse, and the rank of a block diagonal matrix is
the sum of the ranks of its blocks. -/
theorem rk_blkM_zero_C_one {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    {m n n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n') (Fin n) R) :
    rk.rk (m + n') (n + n')
        ((Matrix.fromBlocks A 0 C (1 : Matrix (Fin n') (Fin n') R)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm)
      = rk.rk m n A + (n' : ℝ) := by
  change rk.rk (m + n') (n + n')
      (blockLowerFin A (1 : Matrix (Fin n') (Fin n') R) C) = rk.rk m n A + (n' : ℝ)
  have hkey : blockLowerFin A (1 : Matrix (Fin n') (Fin n') R) C *
      blockLowerFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n') (Fin n') R) (-C)
      = blockLowerFin A (1 : Matrix (Fin n') (Fin n') R) (0 : Matrix (Fin n') (Fin n) R) := by
    rw [blockLowerFin_mul_aux]
    congr 1 <;> simp
  have hcd : blockLowerFin A (1 : Matrix (Fin n') (Fin n') R) (0 : Matrix (Fin n') (Fin n) R)
      = blockDiagFin A (1 : Matrix (Fin n') (Fin n') R) := rfl
  have hUU' : blockLowerFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n') (Fin n') R) (-C) *
      blockLowerFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n') (Fin n') R) C = 1 := by
    rw [blockLowerFin_mul_aux]
    convert blockLowerFin_one_aux (R := R) n n' using 2 <;> simp
  have hmain : rk.rk (m + n') (n + n')
      (blockLowerFin A (1 : Matrix (Fin n') (Fin n') R) C *
        blockLowerFin (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n') (Fin n') R) (-C))
      = rk.rk (m + n') (n + n') (blockLowerFin A (1 : Matrix (Fin n') (Fin n') R) C) :=
    Work.ORHughesFree.SylvesterRank.rk_eq_of_mul_right_inverse rk _ _ _ hUU'
  rw [← hmain, hkey, hcd, rk.rk_blockDiag, Work.ORHughesFree.RankAPI.rk_one_fin]

end Work.ORHughesFree.Epic
