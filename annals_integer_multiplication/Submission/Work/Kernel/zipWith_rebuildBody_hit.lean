import Mathlib
import Submission.Work.Kernel.zipWithDefs

namespace Work.Kernel

/-- One iteration of the rebuild loop of `zipWith` in the *hit* case: the top glyph of stack 3 is
exactly the boundary marker `gMark`, so `zipWith_rebuildBody` pops it from stack 3 and sets the loop
flag to `eos`, stopping the loop. Nothing else is changed.

Cost: `1` (`peek`) `+ 1` (`ite` test) `+ 1` (`pop`) `+ 1` (`set`) `= 4`. -/
theorem zipWith_rebuildBody_hit (main : HvdH.Cmd) {s : HvdH.State} {B3 : List HvdH.Glyph}
    (h3 : s.stk 3 = Work.Layout.gMark :: B3)
    (hreg : s.reg Work.Layout.rLoopG = HvdH.Glyph.cons) :
    ∃ s' n, HvdH.Eval main Work.Kernel.zipWith_rebuildBody s s' n ∧ n ≤ 4 ∧
      s'.stk 3 = B3 ∧ s'.stk 0 = s.stk 0 ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.eos ∧
      (∀ j, j ≠ 0 → j ≠ 3 → s'.stk j = s.stk j) := by
  rw [Work.Kernel.zipWith_rebuildBody]
  -- the test of the `ite`: `peek` reads the head of stack 3, which is the marker, so the
  -- "hit" branch is taken
  have htest : (HvdH.State.tPeek s (3 : HvdH.Stk) Work.Layout.rA).reg Work.Layout.rA =
      Work.Layout.gMark := by
    simp [HvdH.State.tPeek, HvdH.State.updReg_apply, h3]
  -- the whole run: `peek` (1), `ite` test (1), then `pop 3 rA` (1) and `set rLoopG eos` (1)
  refine ⟨HvdH.State.tSet
      (HvdH.State.tPop (HvdH.State.tPeek s (3 : HvdH.Stk) Work.Layout.rA) (3 : HvdH.Stk)
        Work.Layout.rA)
      Work.Layout.rLoopG HvdH.Glyph.eos, 4, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · exact HvdH.Eval.seq (Work.Kernel.eval_peek main (3 : HvdH.Stk) Work.Layout.rA s)
      (HvdH.Eval.iteT htest
        (HvdH.Eval.seq
          (Work.Kernel.eval_pop main (3 : HvdH.Stk) Work.Layout.rA
            (HvdH.State.tPeek s (3 : HvdH.Stk) Work.Layout.rA))
          (Work.Kernel.eval_set main Work.Layout.rLoopG HvdH.Glyph.eos
            (HvdH.State.tPop (HvdH.State.tPeek s (3 : HvdH.Stk) Work.Layout.rA) (3 : HvdH.Stk)
              Work.Layout.rA))))
  · -- stack 3: the marker is popped, exposing `B3`
    simp [HvdH.State.tSet, HvdH.State.updReg_stk, HvdH.State.tPop, HvdH.State.updStk_apply,
      HvdH.State.tPeek, h3]
  · -- stack 0 is untouched
    simp [HvdH.State.tSet, HvdH.State.updReg_stk, HvdH.State.tPop, HvdH.State.updStk_apply,
      HvdH.State.tPeek]
  · -- the loop flag is set to `eos`
    simp [HvdH.State.tSet, HvdH.State.updReg_apply]
  · -- every stack other than 0 and 3 is untouched
    intro j hj0 hj3
    simp [HvdH.State.tSet, HvdH.State.updReg_stk, HvdH.State.tPop, HvdH.State.updStk_apply,
      HvdH.State.tPeek, hj3]

end Work.Kernel
