import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.mulSEvKit

/-!
# The schoolbook multiplication word: programs

State layout for `mulSProg` (all scratch stacks carry a marker at the bottom of the region the
program uses, so arbitrary pre-existing content below is preserved):

* stack 0 : the value stack, holding `int a :: int b :: rest` to begin with;
* `sA` (1): bits of `|a|`, least significant bit first, above marker `mkA`;
* `sB` (2): bits of `|b|`, least significant bit first, above marker `mkB`;
* `sR` (3): the running remainder `ρ` (`size |a|` bits), above marker `mkR`;
* `sC` (4): the accumulated output bits, most significant first, above marker `mkC`;
* `sS` (5): the two sign glyphs, above marker `mkS`;
* `sT` (6): scratch (addition buffer / bit transport), above marker `mkT`;
* `sW` (7): scratch (saved copy of `sA`), above marker `mkW`;
* `sU` (8): scratch (bit assembly), above marker `mkU`.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace MulS

open HvdH

/-! ## Stacks, markers, registers -/

abbrev sA : Stk := 1
abbrev sB : Stk := 2
abbrev sR : Stk := 3
abbrev sC : Stk := 4
abbrev sS : Stk := 5
abbrev sT : Stk := 6
abbrev sW : Stk := 7
abbrev sU : Stk := 8

abbrev mkA : Glyph := .mk 1
abbrev mkB : Glyph := .mk 2
abbrev mkR : Glyph := .mk 3
abbrev mkC : Glyph := .mk 4
abbrev mkS : Glyph := .mk 5
abbrev mkT : Glyph := .mk 6
abbrev mkW : Glyph := .mk 7
abbrev mkU : Glyph := .mk 8
/-- value written into the loop register to stop a `consume` loop (never `eos`, never a marker) -/
abbrev mkStop : Glyph := .mk 9

abbrev rL : Reg := 0
abbrev rBit : Reg := 1
abbrev rA : Reg := 2
abbrev rRho : Reg := 3
abbrev rCy : Reg := 4
abbrev rS : Reg := 5
abbrev rZ : Reg := 6
abbrev rIe : Reg := 7
abbrev rSign : Reg := 8
abbrev rTmp : Reg := 9
abbrev rOut : Reg := 10

/-! ## `consume`: run a handler on every glyph above a marker -/

/-- One step of `consume`: pop a glyph from `src`; if it is the marker `T`, push it back and stop;
otherwise run `handler` (with the popped glyph in register `r`) and continue. -/
def consumeStep (src : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  .seq (.pop src r)
    (.ite r T (.seq (.push src r) (.set r mkStop)) (.seq handler (.set r .eos)))

def consumeLoop (src : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  .loop r .eos (consumeStep src T r handler)

/-- `consume src T r handler` = `consumeLoop` with the loop register initialised. -/
def consume (src : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  .seq (.set r .eos) (consumeLoop src T r handler)

/-- Move every glyph above the marker `T` on `src` to `dst` (reversing the order). -/
def drain (src dst : Stk) (T : Glyph) (r : Reg) : Cmd := consume src T r (.push dst r)

/-! ## The bit-level full adder -/

/-- both output registers of the adder are set by a two-command leaf -/
def faLeaf (sv cw : Bool) : Cmd := .seq (.set rS (.bit sv)) (.set rCy (.bit cw))

/-- `rS := (rA + rRho + rCy) % 2`, `rCy := (rA + rRho + rCy) / 2`, for bit-valued registers. -/
def fullAdd : Cmd :=
  .ite rA (.bit true)
    (.ite rRho (.bit true)
      (.ite rCy (.bit true) (faLeaf true true) (faLeaf false true))
      (.ite rCy (.bit true) (faLeaf false true) (faLeaf true false)))
    (.ite rRho (.bit true)
      (.ite rCy (.bit true) (faLeaf false true) (faLeaf true false))
      (.ite rCy (.bit true) (faLeaf true false) (faLeaf false false)))

/-! ## Phase 1: peel the two input values off stack 0 -/

def peelProg : Cmd :=
  seqs [ .pop 0 rSign, .push sS rSign,
         consume 0 .iend rL (.push sW rL),
         .pop 0 rTmp,
         consume sW mkW rL (.push sA rL),
         .pop 0 rSign, .push sS rSign,
         consume 0 .iend rL (.push sT rL),
         .pop 0 rTmp,
         consume sT mkT rL (.push sB rL) ]

/-! ## Phase 2: initialise the remainder `ρ` to `|a|` zero bits -/

def initRProg : Cmd :=
  seqs [ consume sA mkA rL (.seq (.push sW rL) (.push sR rZ)),
         consume sW mkW rL (.push sA rL) ]

/-! ## Phase 3: the serial multiplier loop -/

/-- One bit position: `ρ += (β ? α : 0)` with carry, output bit to `sT`. -/
def addABody : Cmd :=
  seqs [ .push sW rL,
         .pop sR rRho,
         .mov rA rL,
         .ite rBit (.bit true) .skip (.set rA (.bit false)),
         fullAdd,
         .push sT rS ]

/-- Add `(β ? |a| : 0)` into `ρ`, output the low bit of the sum, halve `ρ`; restore `sA`. -/
def addAProg : Cmd :=
  seqs [ .set rCy (.bit false),
         consume sA mkA rL addABody,
         .push sT rCy,
         consume sT mkT rL (.push sR rL),
         consume sW mkW rL (.push sA rL),
         .pop sR rOut, .push sC rOut ]

/-- Body of the multiplier loop: `rL` holds the next bit `β` of `|b|`. -/
def mainBody : Cmd := seqs [ .mov rBit rL, addAProg ]

def mainLoopProg : Cmd := consume sB mkB rL mainBody

/-! ## Phase 4: assemble the product -/

/-- drop the (high) zero bits on top of `sC` -/
def stripProg : Cmd :=
  seqs [ .set rL .eos,
         .loop rL .eos (.seq (.peek sC rTmp)
           (.ite rTmp (.bit false) (.seq (.pop sC rTmp) (.set rL .eos)) (.set rL mkStop))) ]

/-- compute the sign of the product into `rSign` from the two stored sign glyphs -/
def sgnProg : Cmd :=
  seqs [ .pop sS rBit, .pop sS rA, .pop sS rTmp,
         .ite rA .neg (.ite rBit .neg (.set rSign .pos) (.set rSign .neg))
                     (.ite rBit .neg (.set rSign .neg) (.set rSign .pos)) ]

def finalizeProg : Cmd :=
  seqs [ consume sR mkR rL (.push sT rL),
         consume sT mkT rL (.push sU rL),
         consume sC mkC rL (.push sU rL),
         consume sU mkU rL (.push sC rL),
         stripProg,
         .push 0 rIe,
         sgnProg,
         .peek sC rTmp,
         .ite rTmp mkC (.set rSign .pos) .skip,
         consume sC mkC rL (.push 0 rL),
         .push 0 rSign ]

/-! ## Marker bookkeeping -/

def openProg : Cmd :=
  seqs [ .set rTmp mkA, .push sA rTmp,
         .set rTmp mkB, .push sB rTmp,
         .set rTmp mkR, .push sR rTmp,
         .set rTmp mkC, .push sC rTmp,
         .set rTmp mkS, .push sS rTmp,
         .set rTmp mkT, .push sT rTmp,
         .set rTmp mkW, .push sW rTmp,
         .set rTmp mkU, .push sU rTmp,
         .set rZ (.bit false), .set rIe .iend ]

def closeProg : Cmd :=
  seqs [ consume sA mkA rL .skip,
         .pop sA rTmp, .pop sB rTmp, .pop sR rTmp, .pop sC rTmp,
         .pop sT rTmp, .pop sW rTmp, .pop sU rTmp ]

/-- The whole schoolbook multiplication word. -/
def mulSProg : Cmd := seqs [ openProg, peelProg, initRProg, mainLoopProg, finalizeProg, closeProg ]

/-- bits of `n`, least significant first, as glyphs -/
def bitsG (n : ℕ) : List Glyph := n.bits.map Glyph.bit

theorem bitsG_length (n : ℕ) : (bitsG n).length = n.size := by
  simp [bitsG, Nat.size_eq_bits_len]

theorem bitsG_nil (n : ℕ) : bitsG n = [] ↔ n = 0 := by
  rw [bitsG, List.map_eq_nil_iff, ← List.length_eq_zero_iff, Nat.size_eq_bits_len,
    Nat.size_eq_zero]

end MulS
end Work.IntLib
