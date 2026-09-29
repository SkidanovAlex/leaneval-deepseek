import Mathlib
import Submission.Work.Transform.pwBase

/-!
# `Work.Transform.Pw`: definitions for the buffered lockstep scan (`pwScanB`)

This file holds only the definitions and the elementary `decide` facts about the concrete glyphs and
stacks used by the buffered lockstep comparison `Work.Transform.pwScanB`, so that the per-case
lemmas about the loop body can be stated and proved in separate files importing it.

The scan repeatedly peeks at the two stacks `sA` (holding `A`, least significant bit first, above
the marker `gM`) and `sB` (holding `B`).  While both hold a bit it pops one bit from each, pushes
it onto the buffer stack `bA` resp. `bB` (above a marker that the program has pushed), and updates
`reg rFlag` so that it records the comparison of the bits read so far (a difference always
overwrites, so the *last* difference -- the most significant one -- wins).  As soon as one side has
reached its marker it sets the flag (`gLt` when `A` is exhausted first, `gGt` when `B` is, keeping
the accumulated flag when both are exhausted at the same time) and sets `reg rCont` to `gStop`,
which ends the loop.  Crucially the marker-side glyph is *not* popped, so the exhausted side keeps
its marker.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel
open Work.IntLib

/-! ## Concrete parameters -/

/-- Scratch register receiving the glyph peeked from the first stack. -/
def rGA : Reg := 0

/-- Scratch register receiving the glyph peeked from the second stack. -/
def rGB : Reg := 1

/-- Register scratch (`rGA`) differs from the control register. -/
theorem rGA_ne_rCont : rGA ≠ rCont := by decide
/-- Register scratch (`rGA`) differs from the flag register. -/
theorem rGA_ne_rFlag : rGA ≠ rFlag := by decide
/-- Register scratch (`rGB`) differs from the control register. -/
theorem rGB_ne_rCont : rGB ≠ rCont := by decide
/-- Register scratch (`rGB`) differs from the flag register. -/
theorem rGB_ne_rFlag : rGB ≠ rFlag := by decide
/-- The two scratch registers differ. -/
theorem rGA_ne_rGB : rGA ≠ rGB := by decide

/-- The stop glyph differs from the (continue) flag glyph `gEq`. -/
theorem gStop_ne_gEq : gStop ≠ gEq := by decide
/-- `gLt` differs from `gEq`. -/
theorem gLt_ne_gEq : gLt ≠ gEq := by decide
/-- `gGt` differs from `gEq`. -/
theorem gGt_ne_gEq : gGt ≠ gEq := by decide
/-- `gStop` differs from `gLt`. -/
theorem gStop_ne_gLt : gStop ≠ gLt := by decide
/-- `gStop` differs from `gGt`. -/
theorem gStop_ne_gGt : gStop ≠ gGt := by decide
/-- A bit glyph is not the frame marker. -/
theorem bit_ne_gM (b : Bool) : Glyph.bit b ≠ gM := fun h => nomatch h
/-- The frame marker is not a bit glyph. -/
theorem gM_ne_bit' (b : Bool) : gM ≠ Glyph.bit b := fun h => nomatch h

/-! ## The flag -/

/-- Update of the comparison flag after reading bits `a` (from `A`) and `b` (from `B`): a
difference overwrites the flag of the prefixes, equal bits leave it unchanged. -/
def flagStep (f : Glyph) (a b : Bool) : Glyph :=
  if a then (if b then f else gGt) else (if b then gLt else f)

/-- The canonical glyph recording the comparison of the naturals `x` and `y`. -/
def flagOf (x y : ℕ) : Glyph := if x < y then gLt else if x = y then gEq else gGt

/-! ## The loop body and the program -/

/-- The flag part of the loop body, used once both bits have been moved to the buffers: it
overwrites `reg rFlag` with the comparison of the two bits read (`reg rGA` and `reg rGB` hold
them), in the least-significant-first convention. -/
def flagCmd : Cmd :=
  .ite rGA (Glyph.bit true)
    (.ite rGB (Glyph.bit true) .skip (.set rFlag gGt))
    (.ite rGB (Glyph.bit true) (.set rFlag gLt) .skip)

/-- The "move" part of the loop body: pop one glyph from each of the two stacks and push it onto
the corresponding buffer. -/
def moveCmd (sA sB bA bB : Stk) : Cmd :=
  .seq (.pop sA rGA) (.seq (.push bA rGA) (.seq (.pop sB rGB) (.push bB rGB)))

/-- One step of the buffered lockstep scan.  The two `peek`s leave the stacks untouched; if one of
them reads the marker the flag is set and `reg rCont` becomes `gStop`; otherwise one bit is popped
from each stack and pushed onto the corresponding buffer (`moveCmd`) and the flag is updated
(`flagCmd`). -/
def scanBody (sA sB bA bB : Stk) : Cmd :=
  .seq (.peek sA rGA)
   (.seq (.peek sB rGB)
     (.ite rGA gM
       (.ite rGB gM
          (.set rCont gStop)
          (.seq (.set rFlag gLt) (.set rCont gStop)))
       (.ite rGB gM
          (.seq (.set rFlag gGt) (.set rCont gStop))
          (.seq (moveCmd sA sB bA bB) flagCmd))))

/-- The scan loop: run `scanBody` while `reg rCont` is `eos`. -/
def scanLoop (sA sB bA bB : Stk) : Cmd := .loop rCont Glyph.eos (scanBody sA sB bA bB)

/-- The complete buffered scan program: reset the flag and the control register, push a fresh
marker on each of the two buffer stacks, then run the loop. -/
def scanProg (sA sB bA bB : Stk) : Cmd :=
  .seq (.set rFlag gEq)
   (.seq (.set rCont Glyph.eos)
    (.seq (.set rGB gM)
     (.seq (.push bA rGB)
      (.seq (.set rGB gM)
       (.seq (.push bB rGB) (scanLoop sA sB bA bB))))))

end Work.Transform.Pw
