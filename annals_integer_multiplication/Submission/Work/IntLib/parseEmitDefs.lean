import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw

/-!
# IntLib: definitions for the top-level `parse` / `emit` words

This file fixes the (raw, `Glyph`-level) programs and helper notions used by
`Submission/Work/IntLib/parseEmitWord.lean`:

* `splitCmd` dispatches on the input glyph `Glyph.inp a b` in a register and pushes the
  bit glyph(s) contributing to the `x` accumulator (stack 1) and the `y` accumulator (stack 2);
* `splitLoop` is the loop that scans the whole raw input on stack 0, emptying it and filling
  the two accumulators (most recent push first, hence the accumulator of a scanned list `gs` is
  `pushAcc f gs.reverse`);
* `drainAll` moves a whole stack onto another one (until the source is empty), `drainUntil` moves
  a stack onto another one until a frame marker `T` is popped (which is discarded);
* `emitProg` and `parseProg` are the two top-level programs.

Nothing here is proved here (beyond definitional `simp` lemmas): the `Eval` reasoning lives in
`splitGlyph.lean`, `drainLoops.lean`, `splitLoop.lean` and finally `parseEmitWord.lean`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Bits of an input symbol -/

/-- The bit glyph(s) contributed by an optional input bit (`none` contributes nothing). -/
def bitOf (o : Option Bool) : List Glyph := o.elim [] (fun b => [Glyph.bit b])

@[simp] theorem bitOf_some (b : Bool) : bitOf (some b) = [Glyph.bit b] := rfl
@[simp] theorem bitOf_none : bitOf (none : Option Bool) = [] := rfl

/-- The glyphs pushed onto the `x` accumulator by an input glyph. -/
def inX (g : Glyph) : List Glyph := match g with | .inp a _ => bitOf a | _ => []

/-- The glyphs pushed onto the `y` accumulator by an input glyph. -/
def inY (g : Glyph) : List Glyph := match g with | .inp _ b => bitOf b | _ => []

@[simp] theorem inX_inp (a b : Option Bool) : inX (Glyph.inp a b) = bitOf a := rfl
@[simp] theorem inY_inp (a b : Option Bool) : inY (Glyph.inp a b) = bitOf b := rfl

theorem inX_eos : inX (Glyph.eos) = [] := rfl
theorem inY_eos : inY (Glyph.eos) = [] := rfl

/-- Accumulated pushes: `pushAcc f pre` is the content of a stack that has received `f g` for every
`g` of `pre`, oldest push first (so `pre` lists the consumed glyphs with the most recent one first). -/
def pushAcc (f : Glyph → List Glyph) : List Glyph → List Glyph
  | [] => []
  | g :: pre => f g ++ pushAcc f pre

@[simp] theorem pushAcc_cons (f : Glyph → List Glyph) (g : Glyph) (pre : List Glyph) :
    pushAcc f (g :: pre) = f g ++ pushAcc f pre := rfl

@[simp] theorem pushAcc_nil (f : Glyph → List Glyph) : pushAcc f [] = [] := rfl

/-! ## The `split` dispatch -/

/-- Dispatch on the glyph in register `r` (an input glyph `Glyph.inp a b`): push `Glyph.bit a` on
stack 1 and `Glyph.bit b` on stack 2 (nothing for a missing component); any other glyph pushes
nothing. -/
def splitCmd (r : Reg) : Cmd :=
  (Cmd.ite r (Glyph.inp (some true) (some true)) (Cmd.set 6 (Glyph.bit true) ;;; Cmd.push 1 6 ;;; Cmd.set 7 (Glyph.bit true) ;;; Cmd.push 2 7) (Cmd.ite r (Glyph.inp (some true) (some false)) (Cmd.set 6 (Glyph.bit true) ;;; Cmd.push 1 6 ;;; Cmd.set 7 (Glyph.bit false) ;;; Cmd.push 2 7) (Cmd.ite r (Glyph.inp (some true) none) (Cmd.set 6 (Glyph.bit true) ;;; Cmd.push 1 6) (Cmd.ite r (Glyph.inp (some false) (some true)) (Cmd.set 6 (Glyph.bit false) ;;; Cmd.push 1 6 ;;; Cmd.set 7 (Glyph.bit true) ;;; Cmd.push 2 7) (Cmd.ite r (Glyph.inp (some false) (some false)) (Cmd.set 6 (Glyph.bit false) ;;; Cmd.push 1 6 ;;; Cmd.set 7 (Glyph.bit false) ;;; Cmd.push 2 7) (Cmd.ite r (Glyph.inp (some false) none) (Cmd.set 6 (Glyph.bit false) ;;; Cmd.push 1 6) (Cmd.ite r (Glyph.inp none (some true)) (Cmd.set 7 (Glyph.bit true) ;;; Cmd.push 2 7) (Cmd.ite r (Glyph.inp none (some false)) (Cmd.set 7 (Glyph.bit false) ;;; Cmd.push 2 7) (Cmd.ite r (Glyph.inp none none) (Cmd.skip) Cmd.skip)))))))))

/-- One iteration of the splitting scan: pop a glyph from stack 0; `eos` means the input is
exhausted (set register `r` to `mk 15` to leave the loop), otherwise dispatch with `splitCmd` and
reset the test register to `eos`. -/
def splitBody (r : Reg) : Cmd :=
  .pop 0 r ;;; .ite r Glyph.eos (.set r (Glyph.mk 15)) (splitCmd r ;;; .set r Glyph.eos)

/-- The splitting scan loop. -/
def splitLoop (r : Reg) : Cmd := .loop r Glyph.eos (splitBody r)

/-- The splitting scan, with its test register initialised. -/
def splitAll (r : Reg) : Cmd := .set r Glyph.eos ;;; splitLoop r

/-! ## Pure stack-to-stack moves -/

/-- One iteration of `drainAll k k' r`: pop a glyph from stack `k`; an empty stack (`eos`) leaves
the loop, otherwise the glyph is pushed on stack `k'` and the test register is reset. -/
def drainBody (k k' : Stk) (r : Reg) : Cmd :=
  .pop k r ;;; .ite r Glyph.eos (.set r (Glyph.mk 15)) (.push k' r ;;; .set r Glyph.eos)

/-- The loop moving all of stack `k` onto stack `k'`. -/
def drainLoop (k k' : Stk) (r : Reg) : Cmd := .loop r Glyph.eos (drainBody k k' r)

/-- `drainAll k k' r`: move all of stack `k` onto stack `k'`. -/
def drainAll (k k' : Stk) (r : Reg) : Cmd := .set r Glyph.eos ;;; drainLoop k k' r

/-- One iteration of `drainUntil k k' T r`: as `drainBody`, but the loop leaves when the glyph `T`
is popped (the marker `T` is discarded). -/
def drainTBody (k k' : Stk) (T : Glyph) (r : Reg) : Cmd :=
  .pop k r ;;; .ite r T (.set r (Glyph.mk 15)) (.push k' r ;;; .set r Glyph.eos)

/-- The loop moving all of stack `k` above the marker `T` onto stack `k'`. -/
def drainTLoop (k k' : Stk) (T : Glyph) (r : Reg) : Cmd := .loop r Glyph.eos (drainTBody k k' T r)

/-- `drainUntil k k' T r`: move the part of stack `k` above the marker `T` onto stack `k'` and drop
the marker. -/
def drainUntil (k k' : Stk) (T : Glyph) (r : Reg) : Cmd := .set r Glyph.eos ;;; drainTLoop k k' T r

/-- Push the constant glyph `g` on stack `k` (using register `r`). -/
def pushConst (k : Stk) (g : Glyph) (r : Reg) : Cmd := .set r g ;;; .push k r

/-! ## The two top-level programs -/

/-- The `emit` word: `int z` alone on stack 0 becomes the bits of `z` (least significant bit first,
i.e. first bit on top) on stack 1.

Pipeline: drop the sign glyph `pos`; mark stack 2; move all of stack 0 (which is now
`bits ++ [iend]`) onto stack 2 (reversing it to `iend :: bits.reverse`), drop the `iend`, and move
the rest onto stack 1, stopping at the marker. -/
def emitProg : Cmd :=
  .pop 0 5 ;;;
  pushConst 2 (Glyph.mk 1) 5 ;;;
  drainAll 0 2 5 ;;;
  .pop 2 5 ;;;
  drainUntil 2 1 (Glyph.mk 1) 5

/-- The `parse` word: the raw input word on stack 0 becomes `encs [int x, int y]`.

Pipeline: mark stacks 1 and 2; scan the whole input with `splitCmd`, collecting the `x` bits on
stack 1 and the `y` bits on stack 2 (both with the first bit deepest, i.e. in reverse order); push
the terminator `iend` of `y` on stack 0; move the `y` bits from stack 2 onto stack 0 (restoring the
order); push the sign `pos` of `y` and the terminator `iend` of `x`; move the `x` bits from stack 1
onto stack 0; push the sign `pos` of `x`. -/
def parseProg : Cmd :=
  pushConst 1 (Glyph.mk 0) 5 ;;;
  pushConst 2 (Glyph.mk 1) 5 ;;;
  splitAll 5 ;;;
  pushConst 0 Glyph.iend 5 ;;;
  drainUntil 2 0 (Glyph.mk 1) 5 ;;;
  pushConst 0 Glyph.pos 5 ;;;
  pushConst 0 Glyph.iend 5 ;;;
  drainUntil 1 0 (Glyph.mk 0) 5 ;;;
  pushConst 0 Glyph.pos 5

end Work.IntLib
