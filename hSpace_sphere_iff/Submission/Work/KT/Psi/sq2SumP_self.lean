import Mathlib
import Submission.Work.KT.Psi.psi2sum_Aux
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Defs

/-!
# `Work.KT.Psi.sq2SumP_self` — `sq2PartP` of a block sum, reindexed

`sq2PartP ε (p ⊕ q)` is the matrix `(p ⊕ q) ⊗ (p ⊕ q)` cut down by the `ε`-projector
`(1 + ε·swap)/2`, on the index type `Fin (n + m) × Fin (n + m)`.  The companion description
`sq2PartQ ε p q` is the same object on the "unreindexed" index type
`(Fin n ⊕ Fin m) × (Fin n ⊕ Fin m)`, and `psi2sumE n m` is the reindexing equivalence between
the two.  This file proves the two descriptions agree:

`sq2PartP ε (p.sum q) = reindex (psi2sumE p.1 q.1) (psi2sumE p.1 q.1) (sq2PartQ ε p q)`.

The proof is a bookkeeping exercise in `Matrix.reindex`: `Mat.sum` is a `reindex` of the block
diagonal, `psi2sumE = finSumFinEquiv.prodCongr finSumFinEquiv` commutes with the swap, and
`Matrix.reindexRingEquiv` commutes with sums, products, `•`, `1`, Kronecker products and
permutation matrices.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- `sq2PartP ε` of the block sum `p ⊕ q`, written with the block matrix made explicit, equals the
reindexing of `(p ⊕ q) ⊗ (p ⊕ q)` cut down by the `ε`-projector (over the unreindexed index type
`(Fin p.1 ⊕ Fin q.1) × (Fin p.1 ⊕ Fin q.1)`). -/
theorem sq2PartP_sum_eq (ε : ℂ) (p q : Work.KT.Mat A) :
    Work.KT.sq2PartP ε
        ⟨p.1 + q.1, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 q.2)⟩
      = Matrix.reindex (finSumFinEquiv.prodCongr finSumFinEquiv)
          (finSumFinEquiv.prodCongr finSumFinEquiv)
          (Matrix.kroneckerMap (fun x y : A => x * y) (Matrix.fromBlocks p.2 0 0 q.2)
              (Matrix.fromBlocks p.2 0 0 q.2) *
            (algebraMap ℂ A (1 / 2) •
              (1 + algebraMap ℂ A ε •
                Equiv.Perm.permMatrix A
                  (Equiv.prodComm (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1))))) := by
  -- `psi2sumE` commutes with the swap, so conjugating `prodComm` by it gives `prodComm` again.
  have hperm : (finSumFinEquiv.prodCongr finSumFinEquiv).symm.trans
        ((Equiv.prodComm (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1)).trans
          (finSumFinEquiv.prodCongr finSumFinEquiv))
      = Equiv.prodComm (Fin (p.1 + q.1)) (Fin (p.1 + q.1)) := by
    ext x <;> obtain ⟨a, b⟩ := x <;> simp [Equiv.prodCongr]
  show Matrix.kroneckerMap (fun x y : A => x * y)
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 q.2))
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 q.2)) *
      (algebraMap ℂ A (1 / 2) •
        (1 + algebraMap ℂ A ε •
          Equiv.Perm.permMatrix A (Equiv.prodComm (Fin (p.1 + q.1)) (Fin (p.1 + q.1)))))
    = Matrix.reindex (finSumFinEquiv.prodCongr finSumFinEquiv)
        (finSumFinEquiv.prodCongr finSumFinEquiv)
        (Matrix.kroneckerMap (fun x y : A => x * y) (Matrix.fromBlocks p.2 0 0 q.2)
            (Matrix.fromBlocks p.2 0 0 q.2) *
          (algebraMap ℂ A (1 / 2) •
            (1 + algebraMap ℂ A ε •
              Equiv.Perm.permMatrix A
                (Equiv.prodComm (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1)))))
  simp only [Work.KT.reindex_mul',
    ← Matrix.kroneckerMap_reindex (fun x y : A => x * y) finSumFinEquiv finSumFinEquiv finSumFinEquiv
      finSumFinEquiv,
    Work.KT.reindex_smul, Work.KT.reindex_add', Work.KT.reindex_one', Work.KT.reindex_permMatrix]
  rw [hperm]

/-- `sq2PartP` of a block sum agrees with the unreindexed description `sq2PartQ`, transported along
`psi2sumE`. -/
theorem sq2SumP_self {A : Type} [Ring A] [Algebra ℂ A] (ε : ℂ) {p q : Work.KT.Mat A} :
    Work.KT.sq2PartP ε (p.sum q) =
      Matrix.reindex (Work.KT.Psi.psi2sumE p.1 q.1) (Work.KT.Psi.psi2sumE p.1 q.1)
        (Work.KT.Psi.sq2PartQ ε p q) := by
  exact sq2PartP_sum_eq ε p q

end

end Work.KT.Psi
