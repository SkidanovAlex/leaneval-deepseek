import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_le_left

set_option autoImplicit false

namespace Work.ORHughesFree.RankAPI

open Matrix
open Work.ORHughesFree

variable {R : Type*} [Ring R]

/-- A general `2 × 2` block matrix `[[A, B], [C, D]]` with rectangular blocks, reindexed to
`Fin`. -/
def blkG {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin a) (Fin d) R)
    (C : Matrix (Fin c) (Fin b) R) (D : Matrix (Fin c) (Fin d) R) :
    Matrix (Fin (a + c)) (Fin (b + d)) R :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Block multiplication for `blkG`. -/
theorem blkG_mul {a b c d e f : ℕ}
    (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin a) (Fin d) R)
    (C : Matrix (Fin c) (Fin b) R) (D : Matrix (Fin c) (Fin d) R)
    (A' : Matrix (Fin b) (Fin e) R) (B' : Matrix (Fin b) (Fin f) R)
    (C' : Matrix (Fin d) (Fin e) R) (D' : Matrix (Fin d) (Fin f) R) :
    blkG A B C D * blkG A' B' C' D' =
      blkG (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blkG
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks A B C D) (Matrix.fromBlocks A' B' C' D')
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  rw [Matrix.fromBlocks_multiply]

/-- The block identity is the identity. -/
theorem blkG_one (a b : ℕ) :
    blkG (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  unfold blkG
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/-- The rank of `-1_m` is `m`. -/
theorem rk_neg_one (rk : SylvesterRank R) (m : ℕ) :
    rk.rk m m (-(1 : Matrix (Fin m) (Fin m) R)) = m := by
  have h : (-(1 : Matrix (Fin m) (Fin m) R)) * (-(1 : Matrix (Fin m) (Fin m) R)) = 1 := by
    rw [neg_mul_neg, one_mul]
  have h2 := SylvesterRank.rk_eq_of_left_inverse_mul rk
    (-(1 : Matrix (Fin m) (Fin m) R)) (-(1 : Matrix (Fin m) (Fin m) R)) h
    (1 : Matrix (Fin m) (Fin m) R)
  rw [neg_mul, one_mul] at h2
  rw [h2, rk_one_fin rk m]

/-- Swapping the two block rows of a `2 × 2` block matrix does not change the rank (when the
column index set is untouched). -/
theorem blkG_swap {m n k : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    (blkG (a := m) (b := k) (c := n) (d := m) (0 : Matrix (Fin m) (Fin k) R)
      (-(1 : Matrix (Fin m) (Fin m) R)) (A*B) A : Matrix (Fin (m+n)) (Fin (k+m)) R) =
      Matrix.reindex ((((finSumFinEquiv.symm).trans (Equiv.sumComm (Fin m) (Fin n))).trans
        (finSumFinEquiv (m := n) (n := m))).symm) (Equiv.refl (Fin (k+m)))
        (blkG (a := n) (b := k) (c := m) (d := m) (A*B) A 0 (-(1 : Matrix (Fin m) (Fin m) R))) := by
  have hpt : ∀ (u : Fin m ⊕ Fin n) (w : Fin k ⊕ Fin m),
      (Matrix.fromBlocks (A*B) A 0 (-(1 : Matrix (Fin m) (Fin m) R))) (Sum.swap u) w
        = (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin k) R) (-(1 : Matrix (Fin m) (Fin m) R))
            (A*B) A) u w := by
    intro u w
    rcases u with a | a <;> rcases w with c | c <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Sum.swap]
  ext i j
  simp only [blkG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl,
    id_eq, Equiv.symm_symm, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply]
  exact (hpt (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)).symm

/-- **The Sylvester rank inequality.**  For matrices `A : n × m`, `B : m × k` over a ring
carrying a Sylvester rank function,
`rk A + rk B ≤ rk (A * B) + m`.

The proof uses only `blockUpperFin` (`(SMat4)`), `blockDiagFin` (`(SMat3)`) and the two
one-sided-inverse invariance lemmas: with `P = [[B, -1], [0, A]]` one has
`rk P ≥ rk B + rk A`, while `rk P = rk (diag (A B) (-1)) = rk (A * B) + m`. -/
theorem rk_add_rk_le_rk_mul_add (rk : SylvesterRank R) {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    rk.rk n m A + rk.rk m k B ≤ rk.rk n k (A * B) + (m : ℝ) := by
  set P : Matrix (Fin (m+n)) (Fin (k+m)) R :=
    blkG (a := m) (b := k) (c := n) (d := m) B (-(1 : Matrix (Fin m) (Fin m) R)) 0 A with hP
  have hSMat4 : rk.rk m k B + rk.rk n m A ≤ rk.rk (m+n) (k+m) P := by
    have h := rk.rk_blockUpper B A (-(1 : Matrix (Fin m) (Fin m) R))
    rwa [show blockUpperFin B A (-(1 : Matrix (Fin m) (Fin m) R)) = P from rfl] at h
  have hmain : rk.rk (m+n) (k+m) P = rk.rk n k (A * B) + (m : ℝ) := by
    -- Q : right factor, Q * Qi = 1
    set Q : Matrix (Fin (k+m)) (Fin (k+m)) R :=
      blkG (a := k) (b := k) (c := m) (d := m) (1 : Matrix (Fin k) (Fin k) R) 0 B 1 with hQ
    set Qi : Matrix (Fin (k+m)) (Fin (k+m)) R :=
      blkG (a := k) (b := k) (c := m) (d := m) (1 : Matrix (Fin k) (Fin k) R) 0 (-B) 1 with hQi
    have hQQi : Q * Qi = 1 := by
      rw [hQ, hQi]
      rw [blkG_mul]
      simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, neg_mul,
        add_neg_cancel, add_zero, zero_add]
      exact blkG_one k m
    have hPQ : P * Q = blkG (a := m) (b := k) (c := n) (d := m)
        (0 : Matrix (Fin m) (Fin k) R) (-(1 : Matrix (Fin m) (Fin m) R)) (A*B) A := by
      rw [hP, hQ]
      rw [blkG_mul]
      congr 1
      · rw [Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, add_neg_cancel]
      · rw [Matrix.mul_zero, Matrix.neg_mul, Matrix.mul_one, zero_add]
      · rw [Matrix.zero_mul, zero_add]
      · rw [Matrix.zero_mul, zero_add, Matrix.mul_one]
    -- L : left factor for the last step, L * Li = 1
    set L : Matrix (Fin (n+m)) (Fin (n+m)) R :=
      blkG (a := n) (b := n) (c := m) (d := m) (1 : Matrix (Fin n) (Fin n) R) A 0 1 with hL
    set Li : Matrix (Fin (n+m)) (Fin (n+m)) R :=
      blkG (a := n) (b := n) (c := m) (d := m) (1 : Matrix (Fin n) (Fin n) R) (-A) 0 1 with hLi
    have hLiL : Li * L = 1 := by
      rw [hL, hLi]
      rw [blkG_mul]
      simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, neg_mul,
        add_neg_cancel, add_zero, zero_add]
      exact blkG_one n m
    have hLmul : L * blkG (a := n) (b := k) (c := m) (d := m) (A*B) A 0
        (-(1 : Matrix (Fin m) (Fin m) R)) =
        blkG (a := n) (b := k) (c := m) (d := m) (A*B) 0 0 (-(1 : Matrix (Fin m) (Fin m) R)) := by
      rw [hL]
      rw [blkG_mul]
      congr 1
      · rw [Matrix.one_mul, Matrix.mul_zero, add_zero]
      · rw [Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, add_neg_cancel]
      · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
      · rw [Matrix.zero_mul, Matrix.one_mul, zero_add]
    calc rk.rk (m+n) (k+m) P
        = rk.rk (m+n) (k+m) (P * Q) :=
            (SylvesterRank.rk_eq_of_mul_right_inverse rk P Q Qi hQQi).symm
      _ = rk.rk (m+n) (k+m)
            (blkG (a := m) (b := k) (c := n) (d := m)
              (0 : Matrix (Fin m) (Fin k) R) (-(1 : Matrix (Fin m) (Fin m) R)) (A*B) A) := by
            rw [hPQ]
      _ = rk.rk (n+m) (k+m)
            (blkG (a := n) (b := k) (c := m) (d := m) (A*B) A 0
              (-(1 : Matrix (Fin m) (Fin m) R))) := by
            rw [blkG_swap A B]
            exact rk_reindex rk _ _ _
      _ = rk.rk (n+m) (k+m)
            (L * blkG (a := n) (b := k) (c := m) (d := m) (A*B) A 0
              (-(1 : Matrix (Fin m) (Fin m) R))) :=
            (SylvesterRank.rk_eq_of_left_inverse_mul rk L Li hLiL _).symm
      _ = rk.rk (n+m) (k+m)
            (blkG (a := n) (b := k) (c := m) (d := m) (A*B) 0 0
              (-(1 : Matrix (Fin m) (Fin m) R))) := by rw [hLmul]
      _ = rk.rk n k (A * B) + (m : ℝ) := by
            rw [show blkG (a := n) (b := k) (c := m) (d := m) (A*B) 0 0
                  (-(1 : Matrix (Fin m) (Fin m) R)) = blockDiagFin (A*B)
                  (-(1 : Matrix (Fin m) (Fin m) R)) from rfl]
            rw [rk.rk_blockDiag, rk_neg_one]
  linarith [hSMat4, hmain]

theorem rk_mul_eq_of_maxRank {R : Type*} [Ring R] (rk : SylvesterRank R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin m) R)
    (hB : rk.rk m m B = (m : ℝ)) : rk.rk n m (A * B) = rk.rk n m A := by
  have h := rk_add_rk_le_rk_mul_add rk A B
  have hle := rk.rk_mul_le_left A B
  have : rk.rk n m A ≤ rk.rk n m (A * B) := by linarith
  exact le_antisymm hle this

end Work.ORHughesFree.RankAPI
