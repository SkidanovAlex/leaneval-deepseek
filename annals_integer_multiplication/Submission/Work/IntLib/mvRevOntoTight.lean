import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.eval_mvRevOnto

namespace Work.IntLib

open HvdH

/-- Tight-cost form of `eval_mvRevOnto`: the `consume`/`push` loop of `Work.IntLib.consume_push_rev`
costs at most `5 * l.length + 8` (the stated bound there), and the final `pop` adds a single step,
so the whole program `mvRevOnto` runs in at most `5 * l.length + 9` steps. -/
theorem mvRevOntoTight (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (k' : HvdH.Stk)
    (r : HvdH.Reg) (l bk bk' : List HvdH.Glyph) (s : HvdH.State)
    (hT : ∀ g ∈ l, g ≠ T) (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk')
    (hne : k ≠ k') :
    ∃ s' n, HvdH.Eval main (Work.IntLib.mvRevOnto k T k' r) s s' n ∧
      n ≤ 5 * l.length + 9 ∧
      s'.stk k = bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
  obtain ⟨s₁, n₁, hev₁, hn₁, hk₁, hk₁', hfr₁⟩ :=
    consume_push_rev main k T k' r l bk bk' hne hT s hk hk'
  refine ⟨⟨Function.update s₁.reg r T, Function.update s₁.stk k bk⟩, n₁ + 1,
    Eval.seq hev₁ (Eval.pop_cons (main := main) hk₁), by omega, ?_, ?_, ?_⟩
  · simp
  · simpa [Function.update_of_ne (Ne.symm hne)] using hk₁'
  · intro j hj hj'
    simpa [Function.update_of_ne hj] using hfr₁ j hj hj'

end Work.IntLib
