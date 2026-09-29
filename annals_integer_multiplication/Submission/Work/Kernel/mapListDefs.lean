import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# Kernel: `mapList` — program definitions

`HvdH.KernelLib.mapList` maps a StackLang word `q` over the elements of a list value on stack 0.

The program `mapList_prog q` uses the six stacks

* `0` — the value stack;
* `1` — first buffer: the elements of the list, in reverse order, above a frame marker `gMark`;
* `2` — second buffer: the elements of the list, in order, above a frame marker `gMark`;
* `3` — third buffer: the results `y`, in reverse order, above a frame marker `gMark`;
* `4`, `5` — buffer and pending-counter of the value mover `Work.Layout.mvVal` (always restored).

It runs four loops:

* **A** (`mapList_bodyA`): while the top glyph of stack 0 is `cons`, pop it and move the exposed
  element to stack 1; a `nil` glyph is popped and the loop stops.  Afterwards stack 0 carries only
  `rest` and stack 1 carries the elements in reverse order.
* **B** (`mapList_bodyRev`): while the top glyph of stack 1 is not `gMark`, move the top value of
  stack 1 to stack 2.  Afterwards stack 2 carries the elements in order.
* **C** (`mapList_bodyB q`): while the top glyph of stack 2 is not `gMark`, move the top value `x` of
  stack 2 to stack 0 (so that the value stack is exactly `x :: rest`, as the hypothesis on `q`
  requires), run `q`, and move the result `y` to stack 3.
* **D** (`mapList_bodyR`): push the value `nil` on stack 0, then, while the top glyph of stack 3 is
  not `gMark`, move the top value of stack 3 to stack 0 and push a `cons` glyph on top of it: this
  rebuilds `ofList ys` on top of `rest`.

Every value is moved `O(1)` times, so the total cost is `xs.length * (c + K * (L + 1)) + K`.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- Phase A body: peek the top glyph of stack 0; on `nil` pop it and stop, on `cons` pop it and move
the exposed element to stack 1. -/
def mapList_bodyA : Cmd :=
  .seq (.peek 0 Work.Layout.rA)
    (.ite Work.Layout.rA Glyph.nil
      (.seq (.pop 0 Work.Layout.rA) (.set Work.Layout.rLoopG Glyph.eos))
      (.seq (.pop 0 Work.Layout.rA)
        (.seq (Work.Layout.mvVal 0 1 4 5) (.set Work.Layout.rLoopG Glyph.cons))))

/-- Phase B (reversal) body: while the top glyph of stack 1 is not the marker, move the top value of
stack 1 to stack 2. -/
def mapList_bodyRev : Cmd :=
  .seq (.peek 1 Work.Layout.rA)
    (.ite Work.Layout.rA Work.Layout.gMark
      (.set Work.Layout.rLoopG Glyph.eos)
      (.seq (Work.Layout.mvVal 1 2 4 5) (.set Work.Layout.rLoopG Glyph.cons)))

/-- Phase C body: while the top glyph of stack 2 is not the marker, move the top value to stack 0,
run `q`, and move the result to stack 3. -/
def mapList_bodyB (q : Cmd) : Cmd :=
  .seq (.peek 2 Work.Layout.rA)
    (.ite Work.Layout.rA Work.Layout.gMark
      (.set Work.Layout.rLoopG Glyph.eos)
      (.seq (Work.Layout.mvVal 2 0 4 5)
        (.seq q
          (.seq (Work.Layout.mvVal 0 3 4 5) (.set Work.Layout.rLoopG Glyph.cons)))))

/-- Phase D body: while the top glyph of stack 3 is not the marker, move the top value to stack 0
and push a `cons` glyph on top of it. -/
def mapList_bodyR : Cmd :=
  .seq (.peek 3 Work.Layout.rA)
    (.ite Work.Layout.rA Work.Layout.gMark
      (.set Work.Layout.rLoopG Glyph.eos)
      (.seq (Work.Layout.mvVal 3 0 4 5)
        (.seq (Work.Layout.pushConst 0 Glyph.cons) (.set Work.Layout.rLoopG Glyph.cons))))

/-- The whole `mapList` program. -/
def mapList_prog (q : Cmd) : Cmd :=
  Work.Layout.seqs
    [ .set Work.Layout.rLoopG Glyph.cons,
      Work.Layout.pushConst 1 Work.Layout.gMark,
      .loop Work.Layout.rLoopG Glyph.cons mapList_bodyA,
      Work.Layout.pushConst 2 Work.Layout.gMark,
      .set Work.Layout.rLoopG Glyph.cons,
      .loop Work.Layout.rLoopG Glyph.cons mapList_bodyRev,
      .pop 1 Work.Layout.rA,
      Work.Layout.pushConst 3 Work.Layout.gMark,
      .set Work.Layout.rLoopG Glyph.cons,
      .loop Work.Layout.rLoopG Glyph.cons (mapList_bodyB q),
      .pop 2 Work.Layout.rA,
      Work.Layout.pushConst 0 Glyph.nil,
      .set Work.Layout.rLoopG Glyph.cons,
      .loop Work.Layout.rLoopG Glyph.cons mapList_bodyR,
      .pop 3 Work.Layout.rA ]

/-! ## Elementary facts about `encs`/`ofList` -/

@[simp] theorem mapList_ofList_nil : ofList ([] : List Val) = .nil := rfl

@[simp] theorem mapList_ofList_cons (x : Val) (xs : List Val) :
    ofList (x :: xs) = .cons x (ofList xs) := rfl

/-- `encs` of a list with an empty list value on top. -/
theorem mapList_encs_ofList_nil (rest : List Val) :
    encs (ofList ([] : List Val) :: rest) = Glyph.nil :: encs rest := by
  simp [encs, Val.enc]

/-- `encs` of a list with a nonempty list value on top: the first element is exposed. -/
theorem mapList_encs_ofList_cons (x : Val) (xs : List Val) (rest : List Val) :
    encs (ofList (x :: xs) :: rest) = Glyph.cons :: (x.enc ++ encs (ofList xs :: rest)) := by
  simp [encs, Val.enc, List.append_assoc]

/-- `encs` of a list of values: singleton. -/
@[simp] theorem mapList_encs_singleton (x : Val) : encs [x] = x.enc := by simp [encs]

/-- `encs` reverses under appending a singleton on the right. -/
theorem mapList_encs_append_singleton (l : List Val) (x : Val) :
    encs (l ++ [x]) = encs l ++ x.enc := by rw [encs_append, mapList_encs_singleton]

/-- `encs` of the reverse of a cons. -/
theorem mapList_encs_reverse_cons (x : Val) (xs : List Val) :
    encs ((x :: xs).reverse) = encs xs.reverse ++ x.enc := by
  rw [List.reverse_cons, encs_append, mapList_encs_singleton]

/-- The `head`/`tail` decomposition of the encoding of a nonempty list. -/
theorem mapList_encs_eq_head_append {vs : List Val} (h : vs ≠ []) :
    ∃ v vs', vs = v :: vs' ∧ encs vs = v.enc ++ encs vs' := by
  obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil h
  exact ⟨v, vs', rfl, rfl⟩

end Work.Kernel
