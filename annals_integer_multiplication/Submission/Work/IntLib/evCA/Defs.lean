import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.evCarryDefs
import Submission.Work.IntLib.evCA.Infra

/-!
# `IntLib` / `evCarryAddAny`: definitions

The word `Work.IntLib.EvCA.prog` performs one step of the `evalPoly` streaming window, with the
*number* `b` of bits to finalise read from the unary counter `aCW` rather than hardwired: it reads
the digit `h` (whose value encoding sits, reversed, on `aA`), ripples it into the window `W` (bit
region on `aW`, least significant bit on top), and splits the sum `ofBits W + ofBits hbits` at bit
`b` using the unary counter `aCW`:

* the low `b` bits are pushed onto `aO` (on top of the finalised bits), so that after the step
  `ofBits LO' = ofBits LO + 2^{LO.length} · ((ofBits W + h) % 2^b)`,
* the remaining high bits go back onto `aW` as the new window, so that
  `ofBits W' = (ofBits W + h) / 2^b`.

The word is the one analysed in `Work.IntLib.EvC` (`evCarryDefs`, `evCA/*`), decomposed here into
the phases used in the proof:

| phase | program | content |
|---|---|---|
| setup | `progSetup` | `EvC.readA` (move the digit to `aB`), clear the carry, compute the loop flag |
| loop  | `progLoop`  | `EvC.bodyA` repeated `EvC.addN W hbits` times (the ripple addition) |
| tail  | `progTail`  | `EvC.carryA` (final carry) and drop the `iend` |
| pad   | `progPadI`  | push `b - result.length` zero bits onto `aO` |
| final | `progFinal` | move the high bits from `a2` back onto `aW` |

`EvC.addP` (the loop invariant), `EvC.postP` (the state after the tail) and the phase lemmas
`EvC.stepAEv`, `EvC.routeAEv`, `EvC.flagAEv`, `EvC.addLoop_ev`, `EvC.loop_iterate_pred` live in
`Submission/Work/IntLib/evCarryDefs.lean` and `Submission/Work/IntLib/evCA/`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace EvCA

open HvdH

/-! ## The word, in five phases -/

/-- Move the remaining high bits from `a2` back onto the window (reversing the push order). -/
def progFinal : Cmd := Shift.drain a2 aW (Shift.gmk a2) EvC.rGa EvC.rLa

/-- Setup phase: move the reversed encoding of `h` from `aA` to `aB` (so the bits are least
significant on top), drop the sign glyph, clear the carry and initialise the loop flag. -/
def progSetup : Cmd := Work.Layout.seqs [EvC.readA, EvC.flagA, .set EvC.rKa (Glyph.bit false)]

/-- The main ripple-addition loop. -/
def progLoop : Cmd := .loop EvC.rLa Shift.gGo EvC.bodyA

/-- The tail phase: push the final carry (to `aO` or `a2`, according to the counter) and drop the
`iend` terminator of the digit. -/
def progTail : Cmd := EvC.tailA

/-- The padding phase and the final move: push zeros onto `aO` until the counter is empty (so that
exactly `b` bits have been finalised), then move the remaining high bits back onto the window. -/
def progFinish : Cmd := Work.Layout.seqs [EvC.padA, progFinal]

/-- The complete `evCarryAddAny` word.  It never depends on `b`, `h`, `main` or the state: the
number of bits to finalise is read from the unary counter `aCW`. -/
def prog : Cmd := Work.Layout.seqs [progSetup, progLoop, progTail, progFinish]

/-- The state function after the setup phase: the marker `gmk aA` on `aA`, everything else as in
`X` (the digit's encoding has been consumed). -/
def XA (X : Stk → List Glyph) (As : List Glyph) : Stk → List Glyph :=
  Function.update X aA (Shift.gmk aA :: As)

@[simp] theorem XA_self (X : Stk → List Glyph) (As : List Glyph) :
    XA X As aA = Shift.gmk aA :: As := by simp only [XA, Function.update_self]

theorem XA_ne (X : Stk → List Glyph) (As : List Glyph) {j : Stk} (h : j ≠ aA) :
    XA X As j = X j := by simp only [XA, Function.update_of_ne h]

/-! ## Elementary facts about the encoding of `h` -/

/-- The encoding of a natural number is its sign `pos` followed by the bits, least significant
first (`Computability.encodeNat`), then `iend`. -/
theorem enc_int_eq (h : ℕ) :
    Val.enc (.int (h : ℤ)) =
      Glyph.pos :: ((Computability.encodeNat h).map Glyph.bit ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int]
  simp [Int.natAbs_natCast]

/-- The value of the bits of `h` is `h`. -/
theorem ofBits_encodeNat (h : ℕ) : ofBits (Computability.encodeNat h) = h := by
  rw [Work.IntLib.encodeNat_eq_bits]; exact Work.IntLib.ofBits_bits h

/-- The number of bits of `h` is `h.size`. -/
theorem length_encodeNat (h : ℕ) : (Computability.encodeNat h).length = h.size :=
  Work.IntLib.encodeNat_length h

/-- No value encoding contains a frame marker. -/
theorem noMark_enc_int (h : ℕ) : Shift.NoMark (Val.enc (.int (h : ℤ))) := by
  rw [enc_int_eq]
  intro g hg k
  rcases List.mem_cons.mp hg with hg | hg
  · rw [hg]; exact (Shift.gmk_ne_pos k).symm
  · rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
      exact Shift.bit_ne_gmk k b
    · rw [List.mem_singleton.mp hg]; exact (Shift.gmk_ne_iend k).symm

/-- No value encoding contains a frame marker (reversed form). -/
theorem noMark_enc (h : ℕ) : Shift.NoMark (Val.enc (.int (h : ℤ))).reverse := by
  intro g hg k
  exact noMark_enc_int h g (List.mem_reverse.mp hg) k

/-- A list of bits contains no frame marker. -/
theorem noMark_bits (bs : List Bool) : Shift.NoMark (bs.map Glyph.bit) :=
  Shift.noMark_bitsG bs

end EvCA
end Work.IntLib
