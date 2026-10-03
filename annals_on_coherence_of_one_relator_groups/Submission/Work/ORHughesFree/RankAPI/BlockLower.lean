/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The block lower-triangular matrix `[[A, 0], [C, B]]`

`blockUpperFin A B C` (defined in `Submission/Work/ORHughesFree/SylvesterRank.lean`) is the
block matrix `[[A, C], [0, B]]`.  Here we define its lower-triangular counterpart
`blockLowerFin A B C = [[A, 0], [C, B]]`, needed because transposing a block upper-triangular
matrix produces a block lower-triangular one.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

set_option autoImplicit false

namespace Work.ORHughesFree

open Matrix

/-- The block lower-triangular matrix `[[A, 0], [C, B]]` with index types normalized to `Fin`. -/
def blockLowerFin {R : Type*} [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R)
    (C : Matrix (Fin p) (Fin m) R) :
    Matrix (Fin (n + p)) (Fin (m + q)) R :=
  (Matrix.fromBlocks A 0 C B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

end Work.ORHughesFree
