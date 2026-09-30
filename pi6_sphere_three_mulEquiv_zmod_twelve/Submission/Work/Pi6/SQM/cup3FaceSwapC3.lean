import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `faceU`/`faceV` are preserved by the `C3` branch of the pairing involution

`Work.Pi6.SQM.swapC3` is the branch of the master pairing involution `cup3Swap` that starts
from the `C3` index family (the `(δu)∪₃v` indices `(a,b,c,j)`).  This file proves that, just like
the branch `swapL` (see `cup3FaceSwapL`), it does *not* change the two order maps attached to an
index: the `u`-face `⦋n⦌ ⟶ ⦋N3 n m⦌` and the `v`-face `⦋m⦌ ⟶ ⦋N3 n m⦌` of `swapC3 p` are
the faces of `p` itself.  Consequently the term `cup3Term` is invariant under `swapC3`, which is
what makes the mod-2 cancellation of the summands of the `∪₃` coboundary formula work.

The proof is a case analysis on the fifteen branches of `swapC3` (the five regimes
`reg1u/v … reg5u/v`, the eight cluster moves `B*`, and the six immovable cases `C*`, together with
their degenerate sub-cases).  In every branch the two composites of interval maps are compared
vertex by vertex; after unfolding `faceU`/`faceV`, the accessors `C3a …`, `L3k …`, the interval maps
`c3U/c3V/c4U/c4V/lU/lV/t1U/t1V/t2U/t2V` and the transports `shL/sh3/sh4/shT2`, all vertex values are
explicit `if`-expressions in the branch parameters and the resulting arithmetic goals are closed by
`omega`.  The only global input are the four definitional identities `(C3a p).val = a.val`, …,
`(C3j p).val = j.val` recorded as hypotheses so that `omega` can relate the branch conditions
(which mention the accessors) with the goal (which mentions `a`, `b`, `c`, `j` directly).
-/

set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

theorem cup3FaceSwapC3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : Work.Pi6.SQM.T3Idx n m) :
    Work.Pi6.SQM.faceU n m hn hm (Work.Pi6.SQM.swapC3 n m hn hm p) = Work.Pi6.SQM.faceU n m hn hm (Sum.inr (Sum.inl p)) ∧
    Work.Pi6.SQM.faceV n m hn hm (Work.Pi6.SQM.swapC3 n m hn hm p) = Work.Pi6.SQM.faceV n m hn hm (Sum.inr (Sum.inl p)) := by
  rcases p with ⟨⟨a, ⟨b, ⟨c, j⟩⟩⟩, h⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hj := j.isLt
  have hCa : (C3a (⟨(a, ⟨b, ⟨c, j⟩⟩), h⟩ : T3Idx n m)).val = a.val := rfl
  have hCb : (C3b (⟨(a, ⟨b, ⟨c, j⟩⟩), h⟩ : T3Idx n m)).val = b.val := rfl
  have hCc : (C3c (⟨(a, ⟨b, ⟨c, j⟩⟩), h⟩ : T3Idx n m)).val = c.val := rfl
  have hCj : (C3j (⟨(a, ⟨b, ⟨c, j⟩⟩), h⟩ : T3Idx n m)).val = j.val := rfl
  constructor
  · simp only [swapC3]
    split_ifs <;>
      (refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
       apply Fin.ext
       simp only [faceU, c3U, c4U, lU, t1U, t2U, idxL, idxC3, idxC4, idxT1, idxT2, mkT3, mkT4,
         mkL, mkT1, mkT2, C3a, C3b, C3c, C3j, C3h, C4a, C4b, C4c, C4j, C4h, L3k, L3a, L3b, L3c,
         L3h, CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup3V_val, cup2U_val,
         cup2V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
       split_ifs <;> omega)
  · simp only [swapC3]
    split_ifs <;>
      (refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
       apply Fin.ext
       simp only [faceV, c3V, c4V, lV, t1V, t2V, idxL, idxC3, idxC4, idxT1, idxT2, mkT3, mkT4,
         mkL, mkT1, mkT2, C3a, C3b, C3c, C3j, C3h, C4a, C4b, C4c, C4j, C4h, L3k, L3a, L3b, L3c,
         L3h, CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup3V_val, cup2U_val,
         cup2V_val, Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
       split_ifs <;> omega)

end

end Work.Pi6.SQM
