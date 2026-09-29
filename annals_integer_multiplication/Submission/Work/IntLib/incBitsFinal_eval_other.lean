import Mathlib
import Submission.Work.IntLib.divRaw

namespace Work.IntLib

open HvdH

theorem incBitsFinal_eval_other (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (S : HvdH.Stk)
    (rr rs : HvdH.Reg) (bk : List HvdH.Glyph) (Scont : List HvdH.Glyph) (s : HvdH.State)
    (hne : k ≠ S) (hk : s.stk k = T :: bk) (hS : s.stk S = Scont)
    (hreg : s.reg rr ≠ HvdH.Glyph.bit false) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.incBitsFinal k T S rr rs) s s' n ∧ n ≤ 4 ∧
      s'.stk k = bk ∧ s'.stk S = HvdH.Glyph.bit true :: Scont ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ S → s'.stk j = s.stk j := by
  refine ⟨State.tPush (State.tSet (State.tPop s k rr) rs (Glyph.bit true)) S rs, 4,
    ?_, by norm_num, ?_, ?_, ?_⟩
  · refine Eval.iteF hreg ?_
    exact Eval.seq (Eval.pop k rr s)
      (Eval.seq (Eval.set rs (Glyph.bit true) _) (Eval.push S rs _))
  · simp [State.tPush, State.tSet, State.tPop, hne, hk]
  · have hSk : S ≠ k := fun h => hne h.symm
    simp [State.tPush, State.tSet, State.tPop, hSk, hS]
  · intro j hjk hjS
    simp [State.tPush, State.tSet, State.tPop, hjk, hjS]

end Work.IntLib
