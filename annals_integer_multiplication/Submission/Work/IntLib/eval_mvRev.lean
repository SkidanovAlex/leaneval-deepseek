import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.eval_mvRevOnto

/-!
# `mvRev`: reverse a marked region onto another stack, with a fresh marker

`mvRev k T k' T' r` pushes the marker `T'` on stack `k'`, then moves every glyph of stack `k`
above the frame marker `T` onto `k'` (above `T'`), reversing the order, and finally drops `T`.
This is `mvRevOnto` prefixed by "push the marker `T'` on `k'`" (see
`Submission/Work/IntLib/eval_mvRevOnto.lean`, which proves the raw specification
`Work.IntLib.consume_push_rev` of the loop that does the actual move).

The proof composes four `Eval` steps: `set r T'` (1), `push k' r` (1), the consume loop
(at most `5 * l.length + 8`, `Work.IntLib.consume_push_rev`) and `pop k r` (1).  The total is
`5 * l.length + 11 ≤ 6 * (l.length + 1) + 10`.
-/

namespace Work.IntLib

open HvdH

theorem eval_mvRev (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (k' : HvdH.Stk)
    (T' : HvdH.Glyph) (r : HvdH.Reg) (l bk bk' : List HvdH.Glyph) (s : HvdH.State)
    (hT : ∀ g ∈ l, g ≠ T) (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk')
    (hne : k ≠ k') :
    ∃ s' n, HvdH.Eval main (Work.IntLib.mvRev k T k' T' r) s s' n ∧ n ≤ 6 * (l.length + 1) + 10 ∧
      s'.stk k = bk ∧ s'.stk k' = l.reverse ++ T' :: bk' ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
  -- step 1: `set r T'`
  have h1 : Eval main (.set r T') s ⟨Function.update s.reg r T', s.stk⟩ 1 := Eval.set r T' s
  -- step 2: `push k' r`, so that stack `k'` carries its fresh marker `T'`
  have h2 : Eval main (.push k' r) ⟨Function.update s.reg r T', s.stk⟩
      ⟨Function.update s.reg r T', Function.update s.stk k' (T' :: s.stk k')⟩ 1 := by
    have h := Eval.push (main := main) k' r (⟨Function.update s.reg r T', s.stk⟩ : State)
    simpa using h
  -- step 3: `consume k T r (.push k' r)`, i.e. `consume_push_rev`
  have h2k : (⟨Function.update s.reg r T',
      Function.update s.stk k' (T' :: s.stk k')⟩ : State).stk k = l ++ T :: bk := by
    show Function.update s.stk k' (T' :: s.stk k') k = l ++ T :: bk
    rw [Function.update_of_ne hne, hk]
  have h2k' : (⟨Function.update s.reg r T',
      Function.update s.stk k' (T' :: s.stk k')⟩ : State).stk k' = T' :: bk' := by
    show Function.update s.stk k' (T' :: s.stk k') k' = T' :: bk'
    rw [Function.update_self, hk']
  obtain ⟨s3, n3, hev3, hn3, h3k, h3k', h3fr⟩ :=
    consume_push_rev main k T k' r l bk (T' :: bk') hne hT _ h2k h2k'
  -- step 4: `pop k r`, dropping the marker `T` of stack `k`
  set s4 : State := ⟨Function.update s3.reg r T, Function.update s3.stk k bk⟩ with hs4
  have h4 : Eval main (.pop k r) s3 s4 1 := by
    rw [hs4]
    exact Eval.pop_cons h3k
  have hEval : Eval main (Work.IntLib.mvRev k T k' T' r) s s4 (1 + (1 + (n3 + 1))) :=
    Eval.seq h1 (Eval.seq h2 (Eval.seq hev3 h4))
  have hstk : s4.stk k = bk := by
    rw [hs4]
    show Function.update s3.stk k bk k = bk
    rw [Function.update_self]
  have hstk' : s4.stk k' = l.reverse ++ T' :: bk' := by
    rw [hs4]
    show Function.update s3.stk k bk k' = l.reverse ++ T' :: bk'
    rw [Function.update_of_ne (Ne.symm hne), h3k']
  have hfr : ∀ j : Stk, j ≠ k → j ≠ k' → s4.stk j = s.stk j := by
    intro j hj hj'
    rw [hs4]
    show Function.update s3.stk k bk j = s.stk j
    rw [Function.update_of_ne hj, h3fr j hj hj']
    show Function.update s.stk k' (T' :: s.stk k') j = s.stk j
    rw [Function.update_of_ne hj']
  exact ⟨s4, 1 + (1 + (n3 + 1)), hEval, by omega, hstk, hstk', hfr⟩

end Work.IntLib
