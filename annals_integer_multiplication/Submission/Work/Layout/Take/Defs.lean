import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Kernel.Raw

/-!
# `LayoutLib.take` / `LayoutLib.drop`: definitions

Programs splitting the list `ofList xs` (top of stack `0`, below an integer `k`) after `k` elements.

The five scratch stacks used are `sS`, `sT_x` (elements moved out of the list), `sD`, `sDp`
(unary counters) and `sBit` (the binary counter / bits of `k`); every one of them receives a
frame marker `gMark` at the very beginning and is drained back to that marker at the end, so that
the whole program restores all stacks other than `0`.  `sTmp`, `sX`, `sY` are scratch spaces of
the sub-routines (`sX`, `sY` for `mvVal`, `sTmp` for the carry of the decrement) and are restored
by those sub-routines themselves.

The bits of the integer value on top of stack `0` are read onto `sBit` (least significant bit
first, above the frame marker); the list is then walked, moving every element to `sS` (the first
element of the list ends deepest) while one unary unit `gU` per element is pushed on `sD`; the
binary counter on `sBit` is then decremented once per unit available on `sD` (the units used are
moved to `sDp`); the remaining units of `sD` tell how many elements are to be moved from `sS` to
`sT_x` (this is `len - min k len`: `0` when `k ≥ len`, `len - k` otherwise); finally the answer
`ofList` is rebuilt on stack `0` from `sS` or from `sT_x` (the elements of `sS`/`sT_x` are stored with
the *last* element deepest, so `ofList` of the reverse of the list they show is the value built).
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## The scratch stacks, registers and markers -/

/-- scratch stack holding the elements moved out of the list -/
def sS : Stk := 1
/-- second scratch stack for elements -/
def sT_x : Stk := 2
/-- unary counter (one `gU` per element of the list) -/
def sD : Stk := 3
/-- unary counter of the units consumed by the decrement loop -/
def sDp : Stk := 4
/-- scratch (carry of the decrement, buffered bits) -/
def sTmp : Stk := 5
/-- the bits of the integer `k` (LSB first) above the frame marker -/
def sBit : Stk := 6
/-- first scratch stack of `mvVal` -/
def sX : Stk := 7
/-- second scratch stack of `mvVal` -/
def sY : Stk := 8

/-- loop driver register -/
def rG : Reg := 5
/-- general purpose register -/
def rE_x : Reg := 6
/-- secondary loop driver register -/
def rF_tk : Reg := 7

/-- unary unit glyph -/
def gU : Glyph := .mk 10
/-- "continue" glyph of the loop drivers -/
def gCont_x : Glyph := .mk 11

theorem gU_ne_gMark : gU ≠ gMark := by decide
theorem gMark_ne_gU : gMark ≠ gU := by decide
theorem gCont_ne_gMark : gCont_x ≠ gMark := by decide
theorem gMark_ne_gCont_x : gMark ≠ gCont_x := by decide
theorem gU_ne_gCont_x : gU ≠ gCont_x := by decide
theorem gCont_ne_gU : gCont_x ≠ gU := by decide
theorem gU_ne_eos : gU ≠ Glyph.eos := by decide
theorem gU_ne_cons : gU ≠ Glyph.cons := by decide
theorem gU_ne_nil : gU ≠ Glyph.nil := by decide
theorem gU_ne_iend : gU ≠ Glyph.iend := by decide
theorem gCont_ne_eos : gCont_x ≠ Glyph.eos := by decide
theorem gCont_ne_cons : gCont_x ≠ Glyph.cons := by decide
theorem gU_ne_bit (b : Bool) : gU ≠ Glyph.bit b := fun h => by cases h
theorem gCont_ne_bit (b : Bool) : gCont_x ≠ Glyph.bit b := fun h => by cases h
theorem gU_ne_pos : gU ≠ Glyph.pos := fun h => by cases h
theorem gU_ne_neg : gU ≠ Glyph.neg := fun h => by cases h

/-! ## Distinctness of the scratch stacks (proved by `decide`) -/

theorem sS_ne_sT_x : sS ≠ sT_x := by decide
theorem sS_ne_sD : sS ≠ sD := by decide
theorem sS_ne_sDp : sS ≠ sDp := by decide
theorem sS_ne_sTmp : sS ≠ sTmp := by decide
theorem sS_ne_sBit : sS ≠ sBit := by decide
theorem sS_ne_sX : sS ≠ sX := by decide
theorem sS_ne_sY : sS ≠ sY := by decide
theorem sT_ne_sS : sT_x ≠ sS := by decide
theorem sT_ne_sD : sT_x ≠ sD := by decide
theorem sT_ne_sDp : sT_x ≠ sDp := by decide
theorem sT_ne_sTmp : sT_x ≠ sTmp := by decide
theorem sT_ne_sBit : sT_x ≠ sBit := by decide
theorem sT_ne_sX : sT_x ≠ sX := by decide
theorem sT_ne_sY : sT_x ≠ sY := by decide
theorem sD_ne_sS : sD ≠ sS := by decide
theorem sD_ne_sT_x : sD ≠ sT_x := by decide
theorem sD_ne_sDp : sD ≠ sDp := by decide
theorem sD_ne_sTmp : sD ≠ sTmp := by decide
theorem sD_ne_sBit : sD ≠ sBit := by decide
theorem sD_ne_sX : sD ≠ sX := by decide
theorem sD_ne_sY : sD ≠ sY := by decide
theorem sDp_ne_sS : sDp ≠ sS := by decide
theorem sDp_ne_sT_x : sDp ≠ sT_x := by decide
theorem sDp_ne_sD : sDp ≠ sD := by decide
theorem sDp_ne_sTmp : sDp ≠ sTmp := by decide
theorem sDp_ne_sBit : sDp ≠ sBit := by decide
theorem sDp_ne_sX : sDp ≠ sX := by decide
theorem sDp_ne_sY : sDp ≠ sY := by decide
theorem sTmp_ne_sS : sTmp ≠ sS := by decide
theorem sTmp_ne_sT_x : sTmp ≠ sT_x := by decide
theorem sTmp_ne_sD : sTmp ≠ sD := by decide
theorem sTmp_ne_sDp : sTmp ≠ sDp := by decide
theorem sTmp_ne_sBit : sTmp ≠ sBit := by decide
theorem sTmp_ne_sX : sTmp ≠ sX := by decide
theorem sTmp_ne_sY : sTmp ≠ sY := by decide
theorem sBit_ne_sS : sBit ≠ sS := by decide
theorem sBit_ne_sT_x : sBit ≠ sT_x := by decide
theorem sBit_ne_sD : sBit ≠ sD := by decide
theorem sBit_ne_sDp : sBit ≠ sDp := by decide
theorem sBit_ne_sTmp : sBit ≠ sTmp := by decide
theorem sBit_ne_sX : sBit ≠ sX := by decide
theorem sBit_ne_sY : sBit ≠ sY := by decide
theorem sX_ne_sS : sX ≠ sS := by decide
theorem sX_ne_sT_x : sX ≠ sT_x := by decide
theorem sX_ne_sD : sX ≠ sD := by decide
theorem sX_ne_sDp : sX ≠ sDp := by decide
theorem sX_ne_sTmp : sX ≠ sTmp := by decide
theorem sX_ne_sBit : sX ≠ sBit := by decide
theorem sX_ne_sY : sX ≠ sY := by decide
theorem sY_ne_sS : sY ≠ sS := by decide
theorem sY_ne_sT_x : sY ≠ sT_x := by decide
theorem sY_ne_sD : sY ≠ sD := by decide
theorem sY_ne_sDp : sY ≠ sDp := by decide
theorem sY_ne_sTmp : sY ≠ sTmp := by decide
theorem sY_ne_sBit : sY ≠ sBit := by decide
theorem sY_ne_sX : sY ≠ sX := by decide
theorem sS_ne_zero : sS ≠ (0 : Stk) := by decide
theorem zero_ne_sS : (0 : Stk) ≠ sS := by decide
theorem sT_ne_zero : sT_x ≠ (0 : Stk) := by decide
theorem zero_ne_sT_x : (0 : Stk) ≠ sT_x := by decide
theorem sD_ne_zero : sD ≠ (0 : Stk) := by decide
theorem zero_ne_sD : (0 : Stk) ≠ sD := by decide
theorem sDp_ne_zero : sDp ≠ (0 : Stk) := by decide
theorem zero_ne_sDp : (0 : Stk) ≠ sDp := by decide
theorem sTmp_ne_zero : sTmp ≠ (0 : Stk) := by decide
theorem zero_ne_sTmp : (0 : Stk) ≠ sTmp := by decide
theorem sBit_ne_zero : sBit ≠ (0 : Stk) := by decide
theorem zero_ne_sBit : (0 : Stk) ≠ sBit := by decide
theorem sX_ne_zero : sX ≠ (0 : Stk) := by decide
theorem zero_ne_sX : (0 : Stk) ≠ sX := by decide
theorem sY_ne_zero : sY ≠ (0 : Stk) := by decide
theorem zero_ne_sY : (0 : Stk) ≠ sY := by decide

/-! ## Bit strings -/

/-- A list of bits (least significant first) as a list of `bit` glyphs. -/
def bitsG_x (l : List Bool) : List Glyph := l.map Glyph.bit

theorem bitsG_append (l₁ l₂ : List Bool) : bitsG_x (l₁ ++ l₂) = bitsG_x l₁ ++ bitsG_x l₂ := by
  simp [bitsG_x]

theorem bitsG_length_x (l : List Bool) : (bitsG_x l).length = l.length := by simp [bitsG_x]

theorem bitsG_nil : bitsG_x ([] : List Bool) = [] := rfl

theorem bitsG_reverse_x (l : List Bool) : bitsG_x l.reverse = (bitsG_x l).reverse := by
  simp [bitsG_x]

/-- `gMark` does not occur in a bit string. -/
theorem gMark_notMem_bitsG_x (l : List Bool) : gMark ∉ bitsG_x l := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact gMark_ne_bit b hb.symm

/-- number of leading `false`s: the number of trailing zeros of the number -/
def tzB : List Bool → ℕ
  | [] => 0
  | true :: _ => 0
  | false :: t => tzB t + 1

/-- decrement of a canonical bit string (LSB first, no leading zeros) -/
def decBits : List Bool → List Bool
  | [] => []
  | false :: t => true :: decBits t
  | true :: t => if t = [] then [] else false :: t

/-- the bits of a natural number, as glyphs -/
theorem enc_int_nat_x (k : ℕ) :
    (Val.int (k : ℤ)).enc = Glyph.pos :: (bitsG_x k.bits ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits]
  simp [bitsG_x, Int.natAbs_natCast]

theorem enc_int_nat_length_x (k : ℕ) : (Val.int (k : ℤ)).enc.length = isz (k : ℤ) :=
  Work.IntLib.vsz_int (k : ℤ)

/-! ## The programs -/

/-- `set rE_x gMark ;; push b rE_x` : push the frame marker on stack `b`. -/
def markPush (b : Stk) : Cmd := seqs [.set rE_x gMark, .push b rE_x]

/-- push a frame marker on every scratch stack -/
def initProg : Cmd := seqs [markPush sS, markPush sT_x, markPush sD, markPush sDp, markPush sBit]

/-- body of the bit-reading loop: pop a bit, push it on `sTmp`, stop at `iend` -/
def readIntBody : Cmd := seqs [.pop 0 rE_x,
  .ite rE_x Glyph.iend (.set rG Glyph.eos) (seqs [.push sTmp rE_x, .set rG gCont_x])]

/-- Read the bits of the integer value on top of stack `0` (dropping sign and `iend`) and leave
them, least significant bit first, on top of stack `sBit` (in normal order).  Bits are pushed on
`sTmp` and then moved back with `mvB`, which reverses them. -/
def readIntProg : Cmd := seqs [.set rE_x gMark, .push sTmp rE_x, .pop 0 rE_x, .set rG gCont_x,
  .loop rG gCont_x readIntBody, mvB sTmp sBit]

/-- body of the list-walking loop: pop a `cons` glyph and move the following element to `sS`,
pushing one `gU` on `sD`; stop at `nil` -/
def walkBody : Cmd := seqs [.pop 0 rE_x,
  .ite rE_x Glyph.cons
    (seqs [mvVal 0 sS sX sY, .set rE_x gU, .push sD rE_x, .set rG gCont_x])
    (.set rG Glyph.eos)]

/-- move every element of the list on stack `0` to `sS` (first element deepest), counting them
in unary on `sD` -/
def walkProg_x : Cmd := seqs [.set rG gCont_x, .loop rG gCont_x walkBody]

/-- body of the decrement scan: pop a bit; `false` becomes `true` on the carry stack `sTmp` and
the scan goes on, the first `true` stops it (it becomes `false`, unless it was the last bit) -/
def decBody : Cmd := seqs [.pop sBit rE_x,
  .ite rE_x (Glyph.bit false)
    (seqs [.set rE_x (Glyph.bit true), .push sTmp rE_x, .set rF_tk gCont_x])
    (.ite rE_x (Glyph.bit true)
      (seqs [.peek sBit rE_x,
        .ite rE_x gMark (.set rF_tk Glyph.eos)
          (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
      (.set rF_tk Glyph.eos))]

/-- decrement the binary counter on `sBit` (bits LSB first, frame marker below) by one -/
def decProg : Cmd := seqs [.set rE_x gMark, .push sTmp rE_x, .set rF_tk gCont_x, .loop rF_tk gCont_x decBody,
  mvB sTmp sBit]

/-- body of the comparison loop: while `sD` has a unit and the counter on `sBit` is non-zero,
consume one unit of `sD` (moving it to `sDp`) and decrement the counter -/
def cmpBody : Cmd := seqs [.peek sD rE_x,
  .ite rE_x gU
    (seqs [.peek sBit rE_x,
      .ite rE_x gMark (.set rG Glyph.eos)
        (seqs [.pop sD rE_x, decProg, .set rE_x gU, .push sDp rE_x, .set rG gCont_x])])
    (.set rG Glyph.eos)]

/-- consume units of `sD` one at a time, decrementing the counter on `sBit`, until either the
counter is `0` or `sD` is exhausted -/
def cmpProg : Cmd := seqs [.set rG gCont_x, .loop rG gCont_x cmpBody]

/-- body of the shift loop: consume one unit of `sD`, moving one element from `sS` to `sT_x` -/
def shiftBody : Cmd := seqs [.peek sD rE_x,
  .ite rE_x gU (seqs [.pop sD rE_x, mvVal sS sT_x sX sY, .set rG gCont_x]) (.set rG Glyph.eos)]

/-- move one element from `sS` to `sT_x` for every unit left on `sD` -/
def shiftProg : Cmd := seqs [.set rG gCont_x, .loop rG gCont_x shiftBody]

/-- body of the counter-driven rebuild loop: if the counter `c` has a unit, move one element of
`b` to stack `0` (in front of a `cons`) -/
def buildNBody (c b : Stk) : Cmd := seqs [.peek c rE_x,
  .ite rE_x gU
    (seqs [.pop c rE_x, mvVal b 0 sX sY, .set rE_x Glyph.cons, .push 0 rE_x, .set rG gCont_x])
    (.set rG Glyph.eos)]

/-- Rebuild `ofList ((zs.take n).reverse)` on stack `0` from a stack `b` holding `encs zs` above
its frame marker, driven by `n` unary units on the counter stack `c`.  Every element moved is
consed in front of the accumulator, and the last element moved lands deepest, so the rebuilt value
is `ofList` of the reverse of the prefix `zs.take n` that was moved. -/
def buildNProg (c b : Stk) : Cmd := seqs [.set rE_x Glyph.nil, .push 0 rE_x, .set rG gCont_x,
  .loop rG gCont_x (buildNBody c b)]

/-- body of the drain loop: pop a glyph, stop after popping the frame marker -/
def drainBody_x (b : Stk) : Cmd := seqs [.pop b rE_x,
  .ite rE_x gMark (.set rG Glyph.eos) (.set rG gCont_x)]

/-- discard everything on stack `b` down to and including its frame marker -/
def drainProg (b : Stk) : Cmd := seqs [.set rG gCont_x, .loop rG gCont_x (drainBody_x b)]

/-- One decrement step of the binary counter (what `decProg` computes). -/
def DecStep (main : Cmd) : Prop :=
  ∀ (k : ℕ) (R : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph), 0 < k →
    X sBit = bitsG_x k.bits ++ gMark :: R →
    ∃ s' n, Ev main decProg ⟨g, X⟩ s' n ∧ n ≤ 20 * (tzB k.bits + 2) ∧
      s'.stk sBit = bitsG_x (k - 1).bits ++ gMark :: R ∧ s'.stk sTmp = X sTmp ∧
      (∀ j, j ≠ sBit → j ≠ sTmp → s'.stk j = X j)

/-- the program computing `ofList (xs.take k)`: after the comparison the counter `sDp` has
`min k len` units and `sS` holds `len - min k len` elements less than at the start, so the first
`min k len` elements of the list (counted bottom-up, i.e. the tail of `sS` moved off by the shift)
are rebuilt on stack `0`. -/
def splitTakeProg : Cmd := seqs [initProg, readIntProg, walkProg_x, cmpProg, shiftProg,
  buildNProg sDp sS, drainProg sS, drainProg sT_x, drainProg sD, drainProg sDp, drainProg sBit]

/-- the program computing `ofList (xs.drop k)`: the counter `sD` is left with `len - min k len`
units and `sS` still holds all `len` elements, so the rebuild loop converts the top
`len - min k len` elements of `sS` into `ofList (xs.drop k)` and the rest is discarded. -/
def splitDropProg : Cmd := seqs [initProg, readIntProg, walkProg_x, cmpProg,
  buildNProg sD sS, drainProg sS, drainProg sT_x, drainProg sD, drainProg sDp, drainProg sBit]

end Work.Layout
