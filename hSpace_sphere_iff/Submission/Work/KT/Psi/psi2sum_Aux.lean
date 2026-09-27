import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.psi2sum_Setup

/-!
# `Work.KT.Psi.psi2sum_Aux` — shared data for `psi2Cls_sum`

Additivity of `ψ²` on generators is proved by writing `sq2Part ε (p ⊕ q)` as an explicit block
matrix over the index set `(Fin n × Fin n) ⊕ ((Fin n × Fin m) ⊕ (Fin m × Fin n)) ⊕ (Fin m × Fin m)`
(with `n = p.1`, `m = q.1`) and observing that the two "mixed" blocks `p ⊗ q` and `q ⊗ p` cancel
between `ε = 1` and `ε = -1`.

* `psi2sumE` reindexes `(Fin n ⊕ Fin m) × (Fin n ⊕ Fin m)` to `Fin (n+m) × Fin (n+m)` through
  `finSumFinEquiv` (the equivalence implicit in `Mat.sum`).
* `sq2PartQ ε p q` is `(p ⊕ q) ⊗ (p ⊕ q)` cut down by the `ε`-projector, on the "unreindexed"
  index `(Fin p.1 ⊕ Fin q.1) × (Fin p.1 ⊕ Fin q.1)`.
* `psi2sumB p q` is `(p ⊕ q) ⊗ (p ⊕ q)` in block form, `psi2sumQB` is the swap in block form.

Only definitions live here, so that it can be imported by the helpers proved elsewhere.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The equivalence `(Fin n ⊕ Fin m) × (Fin n ⊕ Fin m) ≃ Fin (n+m) × Fin (n+m)` underlying
`Mat.sum`. -/
def psi2sumE (n m : ℕ) :
    (Fin n ⊕ Fin m) × (Fin n ⊕ Fin m) ≃ Fin (n + m) × Fin (n + m) :=
  finSumFinEquiv.prodCongr finSumFinEquiv

/-- `(p ⊕ q) ⊗ (p ⊕ q)` cut down by the `ε`-projector `(1 + ε·swap)/2`, on the unreindexed index
type `(Fin p.1 ⊕ Fin q.1) × (Fin p.1 ⊕ Fin q.1)`. -/
def sq2PartQ (ε : ℂ) (p q : Mat A) :
    Matrix ((Fin p.1 ⊕ Fin q.1) × (Fin p.1 ⊕ Fin q.1))
      ((Fin p.1 ⊕ Fin q.1) × (Fin p.1 ⊕ Fin q.1)) A :=
  Matrix.kroneckerMap (· * ·) (Matrix.fromBlocks p.2 0 0 q.2) (Matrix.fromBlocks p.2 0 0 q.2) *
    (algebraMap ℂ A (1 / 2) •
      (1 + algebraMap ℂ A ε •
        Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1))))

/-- The Kronecker square `(p ⊕ q) ⊗ (p ⊕ q)` in block form. -/
def psi2sumB (p q : Mat A) :
    Matrix (((Fin p.1 × Fin p.1) ⊕ ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1))) ⊕
      (Fin q.1 × Fin q.1))
      (((Fin p.1 × Fin p.1) ⊕ ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1))) ⊕
      (Fin q.1 × Fin q.1)) A :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (Matrix.kroneckerMap (· * ·) p.2 p.2) 0 0
      (Matrix.fromBlocks (Matrix.kroneckerMap (· * ·) p.2 q.2) 0 0
        (Matrix.kroneckerMap (· * ·) q.2 p.2)))
    0 0 (Matrix.kroneckerMap (· * ·) q.2 q.2)

/-- The swap permutation `(x, y) ↦ (y, x)` in block form. -/
def psi2sumQB (A : Type) [Ring A] (n m : ℕ) :
    Matrix (((Fin n × Fin n) ⊕ ((Fin n × Fin m) ⊕ (Fin m × Fin n))) ⊕
      (Fin m × Fin m))
      (((Fin n × Fin n) ⊕ ((Fin n × Fin m) ⊕ (Fin m × Fin n))) ⊕
      (Fin m × Fin m)) A :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))) 0 0
      (Matrix.fromBlocks 0 (relMat A (Equiv.prodComm (Fin n) (Fin m)))
        (relMat A (Equiv.prodComm (Fin m) (Fin n))) 0))
    0 0 (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin m) (Fin m)))

end

end Work.KT.Psi
