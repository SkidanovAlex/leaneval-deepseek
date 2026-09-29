import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Layout.Move
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.drainValsEv
import Submission.Work.Layout.mvVal_ev_full

/-!
# `Work.Resample.auJoin`: definitions of the "join" word

`auJoin` consumes the run `CH` of `cons`-values sitting on stack 3 (terminated by the glyph
`Glyph.nil`, the encoding of `Val.nil`) and builds the single value `ofList CH.reverse` on top of
stack 0, leaving the `Val.nil` terminator on stack 3.

The loop is driven by the top glyph of stack 3 (a `cons` while there is still a value to move, the
`nil` of the terminator at the end); one iteration moves the top value of stack 3 onto stack 0
(`Work.Layout.mvVal`) and combines it with the accumulator with the single-glyph word `consV`.

This file only fixes the data and the program shape; the one-iteration lemma is
`Work.Resample.auJoinBodyEv`, the loop is `Work.Resample.auJoinLoopEv`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH
open Work.Layout

/-- `auJoinAux vs acc` is the value obtained from `acc` by consing the values of `vs` (top first)
one after the other: the accumulator of the join loop after having processed `vs`. With `acc = nil`
it is `ofList vs.reverse`. -/
def auJoinAux (vs : List Val) (acc : Val) : Val := vs.reverse.foldr Val.cons acc

@[simp] theorem auJoinAux_nil (acc : Val) : auJoinAux [] acc = acc := rfl

/-- One step of the accumulator: processing the top value `v` first. -/
theorem auJoinAux_cons (v : Val) (vs : List Val) (acc : Val) :
    auJoinAux (v :: vs) acc = auJoinAux vs (Val.cons v acc) := by
  simp only [auJoinAux, List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]

/-- From the empty accumulator, `auJoinAux` is `ofList` of the reversed list. -/
theorem auJoinAux_eq_ofList (vs : List Val) : auJoinAux vs .nil = ofList vs.reverse := rfl

/-- One iteration of the join loop: move the top value of stack 3 onto stack 0, combine it with the
accumulator on top of stack 0 (`consV`), and re-read the top glyph of stack 3 into the loop
register `Sk.rH`. -/
def auJoinBody (consV : Cmd) (t d : Stk) : Cmd :=
  .seq (mvVal 3 0 t d) (.seq consV (.peek 3 Sk.rH))

/-- Two scratch stacks, distinct from each other and from stacks `0` and `3`. -/
theorem auJoinFresh : ∃ t d : Stk, t ≠ 0 ∧ t ≠ 3 ∧ d ≠ 0 ∧ d ≠ 3 ∧ t ≠ d := by decide

end Work.Resample
