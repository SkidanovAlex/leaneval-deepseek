import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.psi2sum_Aux
import Submission.Work.KT.Psi.sq2Part_idem
import Submission.Work.KT.Psi.sq2Part_split
import Submission.Work.KT.Psi.sq2Part_MvN
import Submission.Work.KT.Psi.cls_split
import Submission.Work.KT.Psi.cls_conj
import Submission.Work.KT.Psi.cls_orbit
import Submission.Work.KT.Psi.clsI_fromBlocks
import Submission.Work.KT.Psi.midPart_idem
import Submission.Work.KT.Psi.midRaw_reindex_midPart
import Submission.Work.KT.Psi.midRaw_clsI_one_neg
import Submission.Work.KT.Psi.sq2Sum_block_mul
import Submission.Work.KT.Psi.sq2SumP_self
import Submission.Work.KT.Psi.sq2SumQ_quad_eq

/-!
# `Work.KT.Psi.psi2Cls_sum` — additivity of `ψ²` on generators

`sq2Part ε (p ⊕ q)` is `(p ⊕ q) ⊗ (p ⊕ q)` cut down by the projector `(1 + ε·σ)/2` of the swap
`σ`.  Reindexing `(p ⊕ q) ⊗ (p ⊕ q)` by the four-block equivalence `quadEquiv` puts it into the
block form

`sqBlock ε p q = (sq2PartP ε p) ⊕ (midRaw ε p q) ⊕ (sq2PartP ε q)`

(`psi2sumB`, `psi2sumQB` in `psi2sum_Aux` are the block forms of `(p⊕q)⊗(p⊕q)` and of the swap).
The two mixed blocks `p ⊗ q` and `q ⊗ p` sit in the middle block `midRaw ε p q`, where the sign
`ε` only enters through the off-diagonal blocks; conjugating by `diag(1, -1)` exchanges `ε = 1`
and `ε = -1`, so `clsI (midRaw 1 p q) = clsI (midRaw (-1) p q)` (`midRaw_clsI_one_neg`).

Hence the mixed contribution cancels in the difference `ψ² = [Sym²] - [Λ²]`, and only the `p`- and
`q`-blocks survive, giving additivity.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The `ε`-part of `ψ²(p ⊕ q)` splits into the `p`-part, the mixed part and the `q`-part. -/
theorem psi2sum_decomp (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) (ε : ℂ) (hε : ε * ε = 1) :
    cls (sq2Part ε (p.sum q)) =
      cls (sq2Part ε p) + clsI (midRaw ε p q) + cls (sq2Part ε q) := by
  have hidemP : sq2PartP ε p * sq2PartP ε p = sq2PartP ε p := sq2PartP_idem hA ε hε hp
  have hidemQ : sq2PartP ε q * sq2PartP ε q = sq2PartP ε q := sq2PartP_idem hA ε hε hq
  have hidemM : midRaw ε p q * midRaw ε p q = midRaw ε p q := by
    let g : (Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1) ≃
        (Fin p.1 × Fin q.1) ⊕ (Fin p.1 × Fin q.1) :=
      Equiv.sumCongr (Equiv.refl (Fin p.1 × Fin q.1)) (Equiv.prodComm (Fin q.1) (Fin p.1))
    have hmr : Matrix.reindex g g (midRaw ε p q) = midPart ε p q :=
      midRaw_reindex_midPart hA ε p q
    have hmul : Matrix.reindex g g (midRaw ε p q * midRaw ε p q) =
        Matrix.reindex g g (midRaw ε p q) := by
      rw [Work.KT.reindex_mul', hmr, midPart_idem hA ε hε hp hq]
    exact (Matrix.reindexRingEquiv A g).injective hmul
  have hidem2 : (Matrix.fromBlocks (sq2PartP ε p) 0 0 (midRaw ε p q)) *
        (Matrix.fromBlocks (sq2PartP ε p) 0 0 (midRaw ε p q)) =
      Matrix.fromBlocks (sq2PartP ε p) 0 0 (midRaw ε p q) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hidemP, hidemM]
  calc cls (sq2Part ε (p.sum q))
      = clsI (sq2PartP ε (p.sum q)) := cls_sq2PartP_clsI ε (p.sum q)
    _ = clsI (sq2PartQ ε p q) :=
          (congrArg clsI (sq2SumP_self ε)).trans
            (clsI_reindex (psi2sumE p.1 q.1) (sq2PartQ ε p q))
    _ = clsI (Matrix.reindex (quadEquiv (Fin p.1) (Fin q.1)) (quadEquiv (Fin p.1) (Fin q.1))
            (sq2PartQ ε p q)) :=
          (clsI_reindex (quadEquiv (Fin p.1) (Fin q.1)) (sq2PartQ ε p q)).symm
    _ = clsI (sqBlock ε p q) := by rw [sq2SumQ_quad_eq ε, sq2Sum_block_mul ε]
    _ = clsI (sq2PartP ε p) + clsI (midRaw ε p q) + clsI (sq2PartP ε q) := by
          simp only [sqBlock]
          rw [clsI_fromBlocks _ _ hidem2 hidemQ, clsI_fromBlocks _ _ hidemP hidemM]
    _ = cls (sq2Part ε p) + clsI (midRaw ε p q) + cls (sq2Part ε q) := by
          rw [← cls_sq2PartP_clsI ε p, ← cls_sq2PartP_clsI ε q]

theorem psi2Cls_sum {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    psi2Cls (p.sum q) = psi2Cls p + psi2Cls q := by
  have hsum : (p.sum q).IsIdem := Mat.isIdem_sum hp hq
  have hL : psi2Cls (p.sum q) =
      cls (sq2Part 1 (p.sum q)) - cls (sq2Part (-1) (p.sum q)) := by
    unfold psi2Cls; rw [if_pos hsum]
  have hp' : psi2Cls p = cls (sq2Part 1 p) - cls (sq2Part (-1) p) := by
    unfold psi2Cls; rw [if_pos hp]
  have hq' : psi2Cls q = cls (sq2Part 1 q) - cls (sq2Part (-1) q) := by
    unfold psi2Cls; rw [if_pos hq]
  rw [hL, hp', hq', psi2sum_decomp hA hp hq 1 (by norm_num),
    psi2sum_decomp hA hp hq (-1) (by norm_num), midRaw_clsI_one_neg]
  abel

end

end Work.KT.Psi
