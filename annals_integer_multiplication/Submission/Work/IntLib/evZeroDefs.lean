import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base

/-!
# `IntLib` / `evZeroChain`: definitions

The word `zProg` of `Work.IntLib.evZeroChain` replaces the value stack

`[Glyph.nil] ++ Val.enc (.int b) ++ rest`

by `Val.enc (.int 0) ++ rest`, at cost linear in the bit-size of `b`.  Concretely the encoding of
`int b` (for `b : ℕ`) reads

`Glyph.pos :: (Computability.encodeNat b).map Glyph.bit ++ [Glyph.iend]`,

so the program

1. pops the leading `Glyph.nil` (the tail of the chain the caller is building),
2. pops the sign glyph `Glyph.pos`,
3. runs `zLoop`, which pops glyphs from stack `zStk` one by one and stops when it has popped the
   closing `Glyph.iend` (the loop flag `zFl` is set to `zGo` after a bit glyph and to `zStop` after
   the `iend`),
4. pushes `Glyph.iend` and then `Glyph.pos` back, producing `Val.enc (.int 0) = [pos, iend]`.

Only stack `zStk = 0` is touched, so every other stack is restored.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-- The data stack (stack 0). -/
def zStk : Stk := 0

/-- The loop-flag register; the program also uses it as the register it pushes from. -/
def zFl : Reg := 0

/-- The register the skip loop reads its glyphs into. -/
def zRd : Reg := 1

/-- The `loop`-continue flag glyph. -/
def zGo : Glyph := .mk 0

/-- The `loop`-stop flag glyph. -/
def zStop : Glyph := .mk 1

theorem zGo_ne_zStop : zGo ≠ zStop := by decide

theorem bit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := fun h => by cases h
theorem bit_ne_zGo (b : Bool) : Glyph.bit b ≠ zGo := fun h => by cases h
theorem bit_ne_zStop (b : Bool) : Glyph.bit b ≠ zStop := fun h => by cases h
theorem iend_ne_zGo : Glyph.iend ≠ zGo := fun h => by cases h
theorem iend_ne_zStop : Glyph.iend ≠ zStop := fun h => by cases h

/-- The body of the skip loop: pop one glyph from stack `zStk`; if it is `Glyph.iend` set the flag
to `zStop`, otherwise to `zGo`. -/
def zBody : Cmd := seqs [.pop zStk zRd, .ite zRd Glyph.iend (.set zFl zStop) (.set zFl zGo)]

/-- The skip loop: starting with the flag `zGo`, consume glyphs of stack `zStk` (the bits of the
encoding of `int b`, then its closing `iend`). -/
def zLoop : Cmd := .loop zFl zGo zBody

/-- The `evZeroChain` word. -/
def zProg : Cmd :=
  seqs [.pop zStk zFl, .pop zStk zFl, .set zFl zGo, zLoop,
        .set zFl Glyph.iend, .push zStk zFl, .set zFl Glyph.pos, .push zStk zFl]

end Work.IntLib
