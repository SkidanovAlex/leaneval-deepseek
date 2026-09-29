import Mathlib
import Submission.Work.ConvR.flagDefs

namespace Work.ConvR

open HvdH

namespace Work.ConvR
open HvdH

/-- One pass of the read-loop body when the popped glyph is not `iend`: the glyph moves from the
top of `rs` to the top of `rd` and register `rv` holds it.
Cost: `pop` 1 + `push` 1 + `ite` (test + `skip`) 2 = 4. -/
theorem eval_readBody_cont (main : Cmd) (rs rd : Stk) (rf rv : Reg) (g : Glyph)
    (hg : g ≠ Glyph.iend) (l' : List Glyph) (s : State) (hs : s.stk rs = g :: l') :
    Eval main (readBody rs rd rf rv) s (State.tPush (State.tPop s rs rv) rd rv) 4 := by
  unfold readBody
  have h1 : Eval main (Cmd.pop rs rv) s (State.tPop s rs rv) 1 := Eval.pop rs rv s
  have h2 : Eval main (Cmd.push rd rv) (State.tPop s rs rv)
      (State.tPush (State.tPop s rs rv) rd rv) 1 := Eval.push rd rv _
  have h3 : (State.tPop s rs rv).reg rv ≠ Glyph.iend := by
    rw [State.tPop]
    simp only [State.updReg_apply, ite_true, State.updStk_reg]
    rw [hs]
    simpa using hg
  have hI : Eval main (Cmd.ite rv Glyph.iend (Cmd.set rf (Glyph.mk 2)) Cmd.skip)
      (State.tPush (State.tPop s rs rv) rd rv) (State.tPush (State.tPop s rs rv) rd rv) 2 :=
    Eval.iteF h3 (Eval.skip _)
  exact Eval.seq h1 (Eval.seq h2 hI)

end Work.ConvR

/-- Same statement under the plain name `Work.ConvR.eval_readBody_cont`
(the statement as requested was wrapped in its own `namespace Work.ConvR`). -/
theorem eval_readBody_cont (main : Cmd) (rs rd : Stk) (rf rv : Reg) (g : Glyph)
    (hg : g ≠ Glyph.iend) (l' : List Glyph) (s : State) (hs : s.stk rs = g :: l') :
    Eval main (readBody rs rd rf rv) s (State.tPush (State.tPop s rs rv) rd rv) 4 :=
  _root_.Work.ConvR.Work.ConvR.eval_readBody_cont main rs rd rf rv g hg l' s hs

end Work.ConvR
