import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.HopfK.Basic

/-!
# `Work.KT.hkWDefs` — the block matrices of the `W`-construction

Helper definitions for the disk side of the relative product (`Work.KT.hk_relprod`).
For a square matrix `C` of size `p` we set

* `Wblk p C = [[C, 1-C], [1-C, C]]` (size `p+p`), and
* `Dblk p X C = [[X, 0], [0, 1-C]]` (size `p+p`).

`Wblk` is the "involution" of the `W`-construction: for an idempotent `C` it satisfies
`Wblk p C * Wblk p C = 1`, and `Wblk p X (Dblk p X X) (Wblk p X) = diag(1,0)`.
-/

namespace Work.KT

open Matrix

noncomputable section

/-- The block matrix `[[C, 1-C],[1-C, C]]`, reindexed to `Fin (p+p)`. -/
def Wblk {R : Type} [Ring R] (p : ℕ) (C : Matrix (Fin p) (Fin p) R) :
    Matrix (Fin (p + p)) (Fin (p + p)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks C (1 - C) (1 - C) C)

/-- The block matrix `[[X, 0],[0, 1-C]]`, reindexed to `Fin (p+p)`. -/
def Dblk {R : Type} [Ring R] (p : ℕ) (X C : Matrix (Fin p) (Fin p) R) :
    Matrix (Fin (p + p)) (Fin (p + p)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks X 0 0 (1 - C))

end

end Work.KT
