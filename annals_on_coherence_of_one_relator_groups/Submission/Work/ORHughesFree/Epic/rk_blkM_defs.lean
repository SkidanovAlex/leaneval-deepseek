/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary block matrices for `rk_blkM_eq_of_relations`

Given a matrix `B : m' × n'` and a natural number `n`, the matrix `blkB B` is the block
matrix `[[B, 0], [0, 1_n]]` with its two column blocks exchanged, so that it has `n + n'`
columns and its row space sits inside `R^n × R^{n'}`; explicitly, that row space is
`⊤ × (range of the row map of B)`.

Together with the block matrix `RankAPI.blk A 0 0 1` (whose row space inside `R^n × R^{n'}` is
`(range of the row map of A) × ⊤`) this is the pair of matrices used in Malcolmson's
strengthened Schanuel lemma, see `rk_blkM_eq_of_relations`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le

set_option autoImplicit false

namespace Work.ORHughesFree.Epic

open Matrix

/-- The block matrix `[[B, 0], [0, 1_n]]` with its two column blocks exchanged, so that its
columns are indexed by `Fin (n + n')`.  Its row space inside `R^n × R^{n'}` is
`⊤ × (range of the row map of B)`. -/
def blkB {R : Type*} [Zero R] [One R] {m' n n' : ℕ} (B : Matrix (Fin m') (Fin n') R) :
    Matrix (Fin (m' + n)) (Fin (n + n')) R :=
  (Matrix.fromBlocks B 0 0 (1 : Matrix (Fin n) (Fin n) R)).submatrix finSumFinEquiv.symm
    (fun j => finSumFinEquiv.symm ((Work.ORHughesFree.RankAPI.swapFin n n') j))

end Work.ORHughesFree.Epic
