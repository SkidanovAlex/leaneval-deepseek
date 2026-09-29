import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Kernel.Raw

/-!
# `applyAlongWord`: primitive programs

Working stacks of the `applyAlong` implementation carry their data *above* a boundary marker
`gMark` (reused from `Move.lean`), so that at the end they can be cleared back to their original
content (`clearTo`).  This file defines the primitive programs; their `Ev`-level specifications are
proved in separate files (`Submission/Work/Layout/AA/*.lean`).

Registers `rF` (the loop flag), `rP` (peeked glyph), `rQ2`, `rT` are used by the control flow;
`mvVal`/`mvA`/`mvB` clobber registers 0..4, so control registers must avoid those.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- loop flag register (`cons` = continue, `eos` = stop) -/
def rF : Reg := 5
/-- register receiving a peeked glyph -/
def rP : Reg := 6
/-- push-constant register -/
def rQ2 : Reg := 7
/-- scratch register -/
def rT : Reg := 8

/-- push a constant glyph on stack `k` (via register `r`). -/
def pushConst2 (k : Stk) (g : Glyph) (r : Reg) : Cmd := seqs [.set r g, .push k r]

/-- push the boundary marker `gMark` on stack `k`. -/
def pushMark (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [gMark] k r

/-! ## clearing a stack down to its boundary marker -/

/-- body of `clearTo`: stop at the marker, else pop the top glyph. -/
def clearBody (k : Stk) (rr rf : Reg) : Cmd :=
  seqs [.peek k rr,
        .ite rr gMark (.set rf Glyph.eos) (seqs [.pop k rr, .set rf Glyph.cons])]

/-- remove everything above the boundary marker on stack `k`, and the marker itself. -/
def clearTo (k : Stk) (rr rf : Reg) : Cmd :=
  seqs [.set rf Glyph.cons, .loop rf Glyph.cons (clearBody k rr rf), .pop k rr]

/-- remove everything above the boundary marker on stack `k`, keeping the marker (safe to use in the
middle of a run, where `clearTo` would destroy the marker). -/
def clearAbove (k : Stk) (rr rf : Reg) : Cmd :=
  seqs [.set rf Glyph.cons, .loop rf Glyph.cons (clearBody k rr rf)]

/-- move everything above the boundary marker on stack `a` onto stack `b`, *reversing* it (this is what
`decInt` needs). -/
def moveToBody (a b : Stk) (rr rf : Reg) : Cmd :=
  seqs [.peek a rr,
        .ite rr gMark (.set rf Glyph.eos) (seqs [.pop a rr, .push b rr, .set rf Glyph.cons])]

/-- move the content above the boundary marker of `a` onto `b`, reversed (marker left in place). -/
def moveTo (a b : Stk) (rr rf : Reg) : Cmd :=
  seqs [.set rf Glyph.cons, .loop rf Glyph.cons (moveToBody a b rr rf)]

/-! ## value level list operations -/

/-- pop the leading `cons` of stack `a` and move the head value to stack `b`. -/
def unconsTo (a b c d : Stk) (rr : Reg) : Cmd := seqs [.pop a rr, mvVal a b c d]

/-- move the top value of `a` on top of the value of `b` and `cons` it (prepending an element). -/
def prependTo (a b c d : Stk) (rr : Reg) : Cmd :=
  seqs [mvVal a b c d, Work.Kernel.pushGlyphs [Glyph.cons] b rr]

/-- body of `revTo`: pop the leading `cons` of `a`, move the head value to the front of `b`. -/
def revBody (a b c d : Stk) (rr rf rg : Reg) : Cmd :=
  seqs [.peek a rr,
        .ite rr Glyph.cons
          (seqs [.pop a rr, mvVal a b c d,
                 Work.Kernel.pushGlyphs [Glyph.cons] b rg, .set rf Glyph.cons])
          (.set rf Glyph.eos)]

/-- reverse the value list of `a` onto `b` (prepending to the content of `b`): the tailing `nil` of
`(ofList L).enc` is popped and a fresh `nil` is pushed on `b`. -/
def revTo (a b c d : Stk) (rr rf rg : Reg) : Cmd :=
  seqs [.set rf Glyph.cons, .loop rf Glyph.cons (revBody a b c d rr rf rg),
        .pop a rr, Work.Kernel.pushGlyphs [Glyph.nil] b rg]

/-- push the empty list (`nil`) on stack `k`. -/
def pushNil (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [Glyph.nil] k r

/-- reverse the value list of `a` onto the (empty, marker-terminated) stack `b`: the empty list that
the reversed chain ends in is pushed on `b` *first*, and the trailing `nil` of `a` is popped. -/
def revTo2 (a b c d : Stk) (rr rf rg : Reg) : Cmd :=
  seqs [pushNil b rg, .set rf Glyph.cons, .loop rf Glyph.cons (revBody a b c d rr rf rg),
        .pop a rr]

/-! ## integer (counter) operations -/

/-- body of phase 1 of `copyIntTo`: move one glyph of the integer to `t`. -/
def copyIntB1 (a t : Stk) (rr rf : Reg) : Cmd :=
  seqs [.pop a rr, .push t rr, .ite rr Glyph.iend (.set rf Glyph.eos) (.set rf Glyph.cons)]

/-- body of phase 2 of `copyIntTo`: restore the glyph on `a` and copy it to `b`; the loop stops at
the boundary marker of the scratch stack `t`. -/
def copyIntB2 (t a b : Stk) (rr rf : Reg) : Cmd :=
  seqs [.peek t rr,
        .ite rr gMark (.set rf Glyph.eos)
          (seqs [.pop t rr, .push a rr, .push b rr, .set rf Glyph.cons])]

/-- copy the integer value on top of `a` onto `b`, keeping it on `a`; `t` is scratch. -/
def copyIntTo (a b t : Stk) (rr rf : Reg) : Cmd :=
  seqs [.set rf Glyph.cons, .loop rf Glyph.cons (copyIntB1 a t rr rf),
        .set rf Glyph.cons, .loop rf Glyph.cons (copyIntB2 t a b rr rf)]

/-- body of `decInt` phase 1: flip the leading zero bits to one, then the first one to zero. -/
def decB1 (a t : Stk) (rr rf rk : Reg) : Cmd :=
  seqs [.pop a rr,
        .ite rr (Glyph.bit false)
          (seqs [.set rk (Glyph.bit true), .push t rk, .set rf Glyph.cons])
          (seqs [.set rk (Glyph.bit false), .push t rk, .set rf Glyph.eos])]

/-- body of `decInt` phase 2: move the remaining glyphs (bits, then `iend`) onto `t`. -/
def decB2 (a t : Stk) (rr rf : Reg) : Cmd :=
  seqs [.pop a rr, .push t rr, .ite rr Glyph.iend (.set rf Glyph.eos) (.set rf Glyph.cons)]

/-- decrement the natural-number counter at the top of `a` (assumed `≥ 1`); `t` is scratch (used
empty above its marker: it receives the flipped low bits, then the remaining bits and the `iend`).
`moveTo` reverses the temporary back onto `a`, which restores the least-significant-first order. -/
def decInt (a t : Stk) (rr rf rk rs rt : Reg) : Cmd :=
  seqs [.pop a rs,
        .set rf Glyph.cons, .loop rf Glyph.cons (decB1 a t rr rf rk),
        .set rf Glyph.cons, .loop rf Glyph.cons (decB2 a t rr rf),
        .pop t rt,
        .peek t rr,
        .ite rr (Glyph.bit false) (seqs [.pop t rr]) .skip,
        .push t rt,
        moveTo t a rr rf,
        .push a rs]

/-- body of `incInt` phase 1: flip the leading one bits to zero, then the first zero to one. -/
def incB1 (a t : Stk) (rr rf rk : Reg) : Cmd :=
  seqs [.pop a rr,
        .ite rr (Glyph.bit true)
          (seqs [.set rk (Glyph.bit false), .push t rk, .set rf Glyph.cons])
          (.ite rr (Glyph.bit false)
            (seqs [.set rk (Glyph.bit true), .push t rk, .set rf Glyph.eos])
            (seqs [.set rk (Glyph.bit true), .push t rk, .push a rr, .set rf Glyph.eos]))]

/-- increment the natural-number counter at the top of `a`; `t` is scratch. -/
def incInt (a t : Stk) (rr rf rk rs : Reg) : Cmd :=
  seqs [.pop a rs,
        .set rf Glyph.cons, .loop rf Glyph.cons (incB1 a t rr rf rk),
        moveTo t a rr rf,
        .push a rs]

/-- test whether the integer on top of `a` is zero; flag register `rf` is set to `cons` if so. -/
def isZeroInt (a : Stk) (rr rf rs : Reg) : Cmd :=
  seqs [.pop a rs, .peek a rr,
        .ite rr Glyph.iend (seqs [.set rf Glyph.cons, .push a rs])
          (seqs [.set rf Glyph.eos, .push a rs])]

/-- test whether the (positive) integer on top of `a` equals one. -/
def isOneInt (a : Stk) (rr rf rs rt : Reg) : Cmd :=
  seqs [.pop a rs, .pop a rt, .peek a rr,
        .ite rr Glyph.iend (seqs [.set rf Glyph.cons, .push a rt, .push a rs])
          (seqs [.set rf Glyph.eos, .push a rt, .push a rs])]

/-- halve (drop the least significant bit of) the counter on top of `a`, assumed `≥ 2`. -/
def halveInt (a : Stk) (rs rt : Reg) : Cmd := seqs [.pop a rs, .pop a rt, .push a rs]

end Work.Layout
