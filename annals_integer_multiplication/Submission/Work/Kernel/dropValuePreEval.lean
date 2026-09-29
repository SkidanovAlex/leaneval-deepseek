import Mathlib
import Submission.Work.Kernel.dropValueDefs
import Submission.Work.Kernel.Raw

namespace Work.Kernel

open HvdH

/-- Extensionality for `HvdH.State` (`State` carries no generated extensionality lemma): two states
agreeing on every register and every stack are equal. -/
theorem dropValuePreEval_state_ext {s t : State}
    (h : ∀ r, s.reg r = t.reg r) (h2 : ∀ k, s.stk k = t.stk k) : s = t := by
  cases s with
  | mk r k =>
    cases t with
    | mk r' k' =>
      simp only [State.mk.injEq]
      exact ⟨funext h, funext h2⟩

/-- The six setup steps of `dropValue_pre` bring an arbitrary state into the canonical scan state `dropValue_iter s (s.stk 0) 1` (one counter token on stack 1, stack 0 untouched).  Definitions and `@[simp]` component lemmas: `Submission/Work/Kernel/dropValueDefs.lean`. -/
theorem dropValuePreEval (main : HvdH.Cmd) (s : HvdH.State) :
    HvdH.Eval main Work.Kernel.dropValue_pre s (Work.Kernel.dropValue_iter s (s.stk 0) 1) 6 := by
  -- `dropValue_pre` is a straight-line program of six primitive commands; run it step by step and
  -- compare the resulting state with `dropValue_iter s (s.stk 0) 1`.
  unfold dropValue_pre
  let A1 : State := s.updReg 3 dropValue_base
  let A2 : State := A1.updStk 1 (A1.reg 3 :: A1.stk 1)
  let A3 : State := A2.updReg 3 dropValue_tok
  let A4 : State := A3.updStk 1 (A3.reg 3 :: A3.stk 1)
  let A5 : State := A4.updReg 2 dropValue_base
  let A6 : State := A5.updReg 1 dropValue_tok
  have e1 : Eval main (.set 3 dropValue_base) s A1 1 := Eval.set 3 dropValue_base s
  have e2 : Eval main (.push 1 3) A1 A2 1 := Eval.push 1 3 A1
  have e3 : Eval main (.set 3 dropValue_tok) A2 A3 1 := Eval.set 3 dropValue_tok A2
  have e4 : Eval main (.push 1 3) A3 A4 1 := Eval.push 1 3 A3
  have e5 : Eval main (.set 2 dropValue_base) A4 A5 1 := Eval.set 2 dropValue_base A4
  have e6 : Eval main (.set 1 dropValue_tok) A5 A6 1 := Eval.set 1 dropValue_tok A5
  have hall : Eval main dropValue_pre s A6 6 :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))
  have hstate : A6 = dropValue_iter s (s.stk 0) 1 := by
    apply dropValuePreEval_state_ext
    · intro r
      -- registers 1, 2, 3 are overwritten (`1 → tok`, `2 → base`, `3 → tok`), the rest survive
      simp only [A6, A5, A4, A3, A2, A1, dropValue_iter, State.updReg_apply]
      by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;> simp_all
    · intro k
      -- stack 1 receives `base` then `tok` above the untouched tail `s.stk 1`; stack 0 is untouched
      simp only [A6, A5, A4, A3, A2, A1, dropValue_iter, State.updReg_apply,
        State.updStk_self, dropValue_stk1, List.replicate_one, List.cons_append, List.nil_append]
      by_cases h1 : k = 1 <;> by_cases h0 : k = 0 <;> simp_all
  rw [hstate] at hall
  exact hall

end Work.Kernel
