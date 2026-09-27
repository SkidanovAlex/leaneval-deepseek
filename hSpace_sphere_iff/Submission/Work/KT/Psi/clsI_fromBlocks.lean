import Mathlib
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Defs

/-!
# `Work.KT.Psi.clsI_fromBlocks`

The `K₀`-class of the block-diagonal matrix `a ⊕ b = fromBlocks a 0 0 b` (over the sum index
type `ι ⊕ κ`) is the sum of the classes of `a` and `b`, for idempotent `a`, `b`.

The computation is a bookkeeping exercise in reindexing: `clsI` of a matrix over an arbitrary
finite index type is `cls` of any `Fin n`-reindexing of it (`clsI_eq`), a block-diagonal
idempotent reindexes along `sumCongr` to the block diagonal of the reindexed blocks
(`reindex_sumCongr_fromBlocks_zero`), and `cls` is additive over the block sum of `Mat`s
(`cls_sum`).  The two auxiliary lemmas below record the reindexing/idempotency facts.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- Reindexing a block-diagonal matrix along a sum of equivalences: the two diagonal blocks are
reindexed independently. -/
theorem reindex_sumCongr_fromBlocks_zero {R : Type} [Ring R] {ι κ ι' κ' : Type}
    (e : ι ≃ ι') (f : κ ≃ κ') (A : Matrix ι ι R) (D : Matrix κ κ R) :
    Matrix.reindex (Equiv.sumCongr e f) (Equiv.sumCongr e f)
        (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (Matrix.reindex e e A) 0 0 (Matrix.reindex f f D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.sumCongr_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- `Mat.ofIdx` of a matrix is idempotent exactly when the matrix is. -/
theorem isIdem_ofIdx_iff {R : Type} [Ring R] {ι : Type} [Fintype ι]
    (M : Matrix ι ι R) (n : ℕ) (e : ι ≃ Fin n) :
    (Work.KT.Mat.ofIdx M n e).IsIdem ↔ M * M = M := by
  unfold Work.KT.Mat.IsIdem Work.KT.Mat.ofIdx
  simp only
  rw [← Work.KT.reindex_mul_self]
  constructor
  · intro h; exact (Matrix.reindexRingEquiv R e).injective h
  · intro h; rw [h]

theorem clsI_fromBlocks {R : Type} [Ring R] {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : Matrix ι ι R) (b : Matrix κ κ R) (ha : a * a = a) (hb : b * b = b) :
    Work.KT.Psi.clsI (Matrix.fromBlocks a 0 0 b) = Work.KT.Psi.clsI a + Work.KT.Psi.clsI b := by
  have hsum := Work.KT.cls_sum ((isIdem_ofIdx_iff a (Fintype.card ι) (Fintype.equivFin ι)).mpr ha)
    ((isIdem_ofIdx_iff b (Fintype.card κ) (Fintype.equivFin κ)).mpr hb)
  -- The `Mat` of the block-diagonal matrix is the block sum of the `Mat`s of the two blocks.
  have hmat : Work.KT.Mat.ofIdx (Matrix.fromBlocks a 0 0 b)
        (Fintype.card ι + Fintype.card κ)
        ((Equiv.sumCongr (Fintype.equivFin ι) (Fintype.equivFin κ)).trans finSumFinEquiv)
      = Work.KT.Mat.sum (Work.KT.Mat.ofIdx a (Fintype.card ι) (Fintype.equivFin ι))
          (Work.KT.Mat.ofIdx b (Fintype.card κ) (Fintype.equivFin κ)) := by
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change Matrix.reindex
          ((Equiv.sumCongr (Fintype.equivFin ι) (Fintype.equivFin κ)).trans finSumFinEquiv)
          ((Equiv.sumCongr (Fintype.equivFin ι) (Fintype.equivFin κ)).trans finSumFinEquiv)
          (Matrix.fromBlocks a 0 0 b) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) a) 0 0
          (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) b))
    rw [← Work.KT.reindex_reindex (Equiv.sumCongr (Fintype.equivFin ι) (Fintype.equivFin κ))
      finSumFinEquiv (Matrix.fromBlocks a 0 0 b)]
    rw [reindex_sumCongr_fromBlocks_zero (Fintype.equivFin ι) (Fintype.equivFin κ) a b]
  unfold Work.KT.Psi.clsI Work.KT.clsE
  rw [← hsum, Work.KT.Psi.cls_ofIdx_irrel (Matrix.fromBlocks a 0 0 b)
    (Fintype.equivFin (ι ⊕ κ))
    ((Equiv.sumCongr (Fintype.equivFin ι) (Fintype.equivFin κ)).trans finSumFinEquiv)]
  exact congrArg Work.KT.cls hmat

end

end Work.KT.Psi
