import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left

namespace Work.ORHughesFree.DivisionRank

open Matrix
open Work.ORHughesFree.RankAPI

section Helpers

variable {R : Type*} [Ring R]

/-- The block matrix `[[A, B], [C, D]]` with `Fin n ⊕ Fin n` index sets, reindexed to
`Fin (n + n)`.  This is a common generalization of `blockDiagFin` (`B = C = 0`) and
`blockUpperFin` (`C = 0`). -/
private def blk {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Block multiplication for `blk`. -/
private theorem blk_mul {n : ℕ} (A B C D A' B' C' D' : Matrix (Fin n) (Fin n) R) :
    blk A B C D * blk A' B' C' D' =
      blk (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blk
  rw [Matrix.submatrix_mul_equiv (fromBlocks A B C D) (fromBlocks A' B' C' D')
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  rw [Matrix.fromBlocks_multiply]

/-- The block identity matrix. -/
private theorem blk_one {n : ℕ} :
    blk (R := R) (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

end Helpers

/-- **The rank of an idempotent plus the rank of its complement is the size.**  If `p` is an
idempotent `n × n` matrix over a ring and `rk` is a Sylvester matrix rank function, then
`rk p + rk (1 - p) = n`.

The lower bound is subadditivity applied to `p + (1 - p) = 1`.  For the upper bound, `p` and
`1 - p` are orthogonal idempotents, so the block matrix `[[p, 1-p], [1-p, p]]` is its own inverse;
multiplying `diag(p, 1-p)` by it gives `[[p, 1-p], [0, 0]]`, which factors through the `n`-column
matrix `[p, 1-p]` and therefore has rank at most `n`. -/
theorem rk_idempotent_add_compl {R : Type*} [Ring R] (rk : SylvesterRank R) {n : ℕ}
    (p : Matrix (Fin n) (Fin n) R) (hp : p * p = p) :
    rk.rk n n p + rk.rk n n (1 - p) = n := by
  set f : Matrix (Fin n) (Fin n) R := 1 - p with hf
  have hff : f * f = f := by rw [hf]; noncomm_ring [hp]
  have hpf : p * f = 0 := by rw [hf]; noncomm_ring [hp]
  have hfp : f * p = 0 := by rw [hf]; noncomm_ring [hp]
  have hsum : p + f = 1 := by rw [hf]; abel
  -- The rank of the block diagonal `diag(p, f)` is the sum of the two ranks.
  have hdiag : rk.rk n n p + rk.rk n n f =
      rk.rk (n + n) (n + n) (blk (R := R) p 0 0 f) :=
    (rk.rk_blockDiag p f).symm
  -- `W = [[p, f], [f, p]]` is its own inverse.
  have hWW : blk (R := R) p f f p * blk p f f p = 1 := by
    rw [blk_mul]
    have h1 : p * p + f * f = 1 := by rw [hp, hff, hsum]
    have h2 : p * f + f * p = 0 := by rw [hpf, hfp, add_zero]
    have h3 : f * p + p * f = 0 := by rw [hfp, hpf, add_zero]
    have h4 : f * f + p * p = 1 := by rw [← h1]; abel
    rw [h1, h2, h3, h4, blk_one]
  -- `W * diag(p, f) = [[p, f], [0, 0]]`.
  have hWM : blk (R := R) p f f p * blk p 0 0 f = blk p f 0 0 := by
    rw [blk_mul]
    have h1 : p * p + f * (0 : Matrix (Fin n) (Fin n) R) = p := by
      rw [hp, mul_zero, add_zero]
    have h2 : p * 0 + f * f = f := by rw [hff, mul_zero, zero_add]
    have h3 : f * p + p * 0 = 0 := by rw [hfp, mul_zero, add_zero]
    have h4 : f * 0 + p * f = 0 := by rw [hpf, mul_zero, zero_add]
    rw [h1, h2, h3, h4]
  -- `[[p, f], [0, 0]]` factors through the `n`-column matrix `[p, f]`, so its rank is at most `n`.
  have hbound : rk.rk (n + n) (n + n) (blk (R := R) p f 0 0) ≤ n := by
    let P : Matrix (Fin (n + n)) (Fin n) R :=
      (fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R)).submatrix
        finSumFinEquiv.symm id
    let Q : Matrix (Fin n) (Fin (n + n)) R :=
      (fromCols p f).submatrix id finSumFinEquiv.symm
    have hPQ : blk (R := R) p f 0 0 = P * Q := by
      unfold blk P Q
      rw [← Matrix.submatrix_mul
        (fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R))
        (fromCols p f) finSumFinEquiv.symm id finSumFinEquiv.symm Function.bijective_id]
      rw [Matrix.fromRows_mul_fromCols]
      simp
    calc rk.rk (n + n) (n + n) (blk (R := R) p f 0 0)
        = rk.rk (n + n) (n + n) (P * Q) := by rw [hPQ]
      _ ≤ rk.rk n (n + n) Q := rk.rk_mul_le_right P Q
      _ ≤ n := rk_le_left rk Q
  have hle : rk.rk n n p + rk.rk n n f ≤ n := by
    rw [hdiag]
    calc rk.rk (n + n) (n + n) (blk (R := R) p 0 0 f)
        = rk.rk (n + n) (n + n) (blk p f f p * blk p 0 0 f) :=
          (SylvesterRank.rk_eq_of_left_inverse_mul rk (blk p f f p)
            (blk p f f p) hWW (blk p 0 0 f)).symm
      _ = rk.rk (n + n) (n + n) (blk p f 0 0) := by rw [hWM]
      _ ≤ n := hbound
  have hge : n ≤ rk.rk n n p + rk.rk n n f := by
    have h := rk_add_le rk p f
    rw [hsum, rk_one_fin rk n] at h
    exact h
  exact le_antisymm hle hge

end Work.ORHughesFree.DivisionRank
