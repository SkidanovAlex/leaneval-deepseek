/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Flattening block matrices

`flattenBlocks` turns a `k × l` matrix of `n × n` blocks into a `(k*n) × (l*n)` matrix.  It is the
device used to induce a Sylvester rank function on `Mat_n(U)` from one on `U`
([JZLA20, §2.4] and the proof of Lemma 2.7).
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

open Matrix

/-- Flattening a `k × l` block matrix of `n × n` blocks into a `(k*n) × (l*n)` matrix. -/
def flattenBlocks {R : Type u} {n k l : ℕ}
    (A : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) R)) :
    Matrix (Fin (k * n)) (Fin (l * n)) R :=
  fun i j => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

end Work.ORHughesFree
