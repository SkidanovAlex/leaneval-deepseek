import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.AddSub.EvKit

/-!
# `IntLib` / add–sub: StackLang programs for signed integer addition and subtraction

This file only *defines* the programs (no proofs).  The main target is: given two integer
values `int a :: int b :: rest` on stack 0, produce `int (a + b) :: rest` (resp.
`int (a - b) :: rest`) at cost `O(isz a + isz b)`.

## Encoding reminder

`(Val.int z).enc = [pos|neg] ++ (encodeNat z.natAbs).map Glyph.bit ++ [iend]`, first glyph on
top of stack 0.  So on stack 0 the top value is `a`, the next one `b`.

## Frame discipline

Stacks `1..15` are shared with arbitrary junk.  Every scratch stack `k` used by the program
receives the marker `gmk k = .mk k` as its bottom element (pushed first); all our data lives
strictly above it, and every loop that consumes our data stops at the marker *without*
consuming it.  At the very end `asw_cleanup` pops, for every stack used, everything down to
the marker and then the marker itself, restoring the entry content.

## Bit lists

A stack `k` "holds the bit list `bs`" when the glyphs above its marker are exactly
`bs.map Glyph.bit`; popping yields `bs` from head to tail, i.e. `bs` is stored
least-significant-bit first.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## `Function.update` normalisation (for the state-shaped `Ev` statements) -/

section SimpLemmas

variable {g : Reg → Glyph} {X : Stk → List Glyph}

@[simp] theorem upStk_same (k : Stk) {l : List Glyph} : (Function.update X k l) k = l :=
  Function.update_self k l X

@[simp] theorem upStk_ne {k k' : Stk} (h : k ≠ k') {l : List Glyph} :
    (Function.update X k' l) k = X k := Function.update_of_ne h l X

@[simp] theorem upStk_ne' {k k' : Stk} (h : k' ≠ k) {l : List Glyph} :
    (Function.update X k l) k' = X k' := Function.update_of_ne h l X

@[simp] theorem upReg_same (r : Reg) {c : Glyph} : (Function.update g r c) r = c :=
  Function.update_self r c g

@[simp] theorem upReg_ne {r r' : Reg} (h : r ≠ r') {c : Glyph} :
    (Function.update g r' c) r = g r := Function.update_of_ne h c g

@[simp] theorem upReg_ne' {r r' : Reg} (h : r' ≠ r) {c : Glyph} :
    (Function.update g r c) r' = g r' := Function.update_of_ne h c g

end SimpLemmas

/-! ## Registers, glyphs, stacks -/

def rA : Reg := 0
def rB : Reg := 1
def rC : Reg := 2
def rD : Reg := 3
def rF : Reg := 4
def rS : Reg := 5
def rT : Reg := 6
def rX : Reg := 7
def rY : Reg := 8
def rU : Reg := 9
def rV : Reg := 10
def rW : Reg := 11

/-- loop-continue flag value -/
def gGo : Glyph := .mk 0
/-- loop-stop flag value -/
def gStop : Glyph := .mk 1

/-- The frame marker sitting at the bottom of everything the program puts on scratch stack `k`. -/
def gmk (k : Stk) : Glyph := .mk k

/-- scratch buffer for the two magnitudes, used sequentially -/
def sBuf : Stk := 1
/-- magnitude of the first operand, LSB first, above its marker -/
def sA : Stk := 3
/-- magnitude of the second operand, LSB first, above its marker -/
def sB : Stk := 4
/-- first output: sum of magnitudes, or `|a|-|b|` -/
def sO1 : Stk := 5
/-- second output: `|b|-|a|` -/
def sO2 : Stk := 6
/-- sign glyph of the first operand -/
def sSgA : Stk := 8
/-- sign glyph of the second operand (after the optional flip) -/
def sSgB : Stk := 9

/-! ## Elementary loops -/

/-- Pop glyphs from `a` and push them onto `b`, until the glyph `T` is read; `T` is pushed
back onto `a` and the loop stops.  Register `rF` (≠ `r`) is the loop flag. -/
def asw_drain (a b : Stk) (T : Glyph) (r rF : Reg) : Cmd :=
  seqs [.set rF gGo,
    .loop rF gGo (seqs [.pop a r,
      .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])])]

/-- Pop glyphs from `k` and discard them until the glyph `M` is read; `M` is pushed back. -/
def asw_clearAt (k : Stk) (M : Glyph) (r rF : Reg) : Cmd :=
  seqs [.set rF gGo,
    .loop rF gGo (seqs [.pop k r,
      .ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)])]

/-- `asw_clearAt` followed by removing the marker itself: leaves the content below the marker. -/
def asw_clear (k : Stk) (M : Glyph) (r rF : Reg) : Cmd :=
  seqs [asw_clearAt k M r rF, .pop k r]

/-- Pop the leading `bit false` glyphs of the stack `out` (which are its *leading zeros*,
the magnitude being stored most-significant-bit first at the top); stop at any other glyph
(which is pushed back). -/
def asw_stripLoop (out : Stk) : Cmd :=
  seqs [.set rF gGo,
    .loop rF gGo (seqs [.pop out rT,
      .ite rT (.bit false) (.set rF gGo) (seqs [.push out rT, .set rF gStop])])]

/-! ## Bit-level arithmetic -/

/-- output bit of `x + y + c` -/
def asw_addOutBit (x y c : Bool) : Bool := ((x.toNat + y.toNat + c.toNat) % 2 == 1)

/-- carry of `x + y + c` -/
def asw_addCarry (x y c : Bool) : Bool := ((x.toNat + y.toNat + c.toNat) / 2 == 1)

/-- The digit of `x - y - bw` in two's complement (`= t % 2`), `t = x - y - bw ∈ {-2,-1,0,1}` -/
def asw_subOutBit (x y bw : Bool) : Bool :=
  (((x.toNat : ℤ) - (y.toNat : ℤ) - (bw.toNat : ℤ)) % 2 == 1)

/-- the borrow-out of `x - y - bw` -/
def asw_subBw (x y bw : Bool) : Bool :=
  decide (((x.toNat : ℤ) - (y.toNat : ℤ) - (bw.toNat : ℤ)) < 0)

/-- Emit the bit `owOut` on `out` and set the carry/borrow register to `owBw`. -/
def asw_leaf (owOut owBw : Bool) (rT rbw : Reg) (out : Stk) : Cmd :=
  seqs [.set rT (.bit owOut), .push out rT, .set rbw (.bit owBw)]

/-- The 8-case decision tree computing the sum bit and the carry of `x + y + c`;
registers `rX rY rc` hold `bit x`, `bit y`, `bit c` on entry. -/
def asw_addTree (rX rY rc rT : Reg) (out : Stk) : Cmd :=
  .ite rX (.bit true)
    (.ite rY (.bit true)
      (.ite rc (.bit true)
        (asw_leaf (asw_addOutBit true true true) (asw_addCarry true true true) rT rc out)
        (asw_leaf (asw_addOutBit true true false) (asw_addCarry true true false) rT rc out))
      (.ite rc (.bit true)
        (asw_leaf (asw_addOutBit true false true) (asw_addCarry true false true) rT rc out)
        (asw_leaf (asw_addOutBit true false false) (asw_addCarry true false false) rT rc out)))
    (.ite rY (.bit true)
      (.ite rc (.bit true)
        (asw_leaf (asw_addOutBit false true true) (asw_addCarry false true true) rT rc out)
        (asw_leaf (asw_addOutBit false true false) (asw_addCarry false true false) rT rc out))
      (.ite rc (.bit true)
        (asw_leaf (asw_addOutBit false false true) (asw_addCarry false false true) rT rc out)
        (asw_leaf (asw_addOutBit false false false) (asw_addCarry false false false) rT rc out)))

/-- The 8-case decision tree computing the two's complement digit and the borrow-out of
`x - y - bw`; registers `rX rY rbw` hold `bit x`, `bit y`, `bit bw` on entry. -/
def asw_subTree (rX rY rbw rT : Reg) (out : Stk) : Cmd :=
  .ite rX (.bit true)
    (.ite rY (.bit true)
      (.ite rbw (.bit true)
        (asw_leaf (asw_subOutBit true true true) (asw_subBw true true true) rT rbw out)
        (asw_leaf (asw_subOutBit true true false) (asw_subBw true true false) rT rbw out))
      (.ite rbw (.bit true)
        (asw_leaf (asw_subOutBit true false true) (asw_subBw true false true) rT rbw out)
        (asw_leaf (asw_subOutBit true false false) (asw_subBw true false false) rT rbw out)))
    (.ite rY (.bit true)
      (.ite rbw (.bit true)
        (asw_leaf (asw_subOutBit false true true) (asw_subBw false true true) rT rbw out)
        (asw_leaf (asw_subOutBit false true false) (asw_subBw false true false) rT rbw out))
      (.ite rbw (.bit true)
        (asw_leaf (asw_subOutBit false false true) (asw_subBw false false true) rT rbw out)
        (asw_leaf (asw_subOutBit false false false) (asw_subBw false false false) rT rbw out)))

/-! ## The magnitude adder and subtractor loops -/

/-- One step of the magnitude adder: read one digit of `a` and one of `b` (a `false` digit
if the stack is exhausted), emit the sum digit on `out` and update the carry `rc`. -/
def asw_addBody (a b out : Stk) (rc rT rX rY rU rV rF : Reg) : Cmd :=
  seqs [.peek a rU,
    .ite rU (gmk a) (.set rX (.bit false)) (.pop a rX),
    .peek b rV,
    .ite rV (gmk b) (.set rY (.bit false)) (.pop b rY),
    asw_addTree rX rY rc rT out,
    .set rF gGo,
    .ite rc (.bit false) (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip]

/-- Magnitude adder: `|a| + |b|`, digits least significant first, on `out`. -/
def asw_addLoop (a b out : Stk) : Cmd :=
  seqs [.set rF gGo, .loop rF gGo (asw_addBody a b out rC rT rX rY rU rV rF)]

/-- One step of the simultaneous subtractor: read one digit of `a` and one of `b`, emit the
digit of `|a| - |b|` (two's complement, borrow `rc`) on `o1` and the digit of `|b| - |a|`
(borrow `rd`) on `o2`. -/
def asw_subBody (a b o1 o2 : Stk) (rc rd rT rX rY rU rV rF : Reg) : Cmd :=
  seqs [.peek a rU,
    .ite rU (gmk a) (.set rX (.bit false)) (.pop a rX),
    .peek b rV,
    .ite rV (gmk b) (.set rY (.bit false)) (.pop b rY),
    asw_subTree rX rY rc rT o1,
    asw_subTree rY rX rd rT o2,
    .set rF gGo,
    .ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip]

/-- Simultaneous subtractor: on `o1` the digits of `|a| - |b|` and on `o2` those of
`|b| - |a|`, both modulo `2^n` (`n` = number of digits); the borrows are left in `rC`, `rD`. -/
def asw_subLoop (a b o1 o2 : Stk) : Cmd :=
  seqs [.set rF gGo, .set rC (.bit false), .set rD (.bit false),
    .loop rF gGo (asw_subBody a b o1 o2 rC rD rT rX rY rU rV rF)]

/-! ## Parsing, dispatch, output -/

/-- Rename `rB` from `pos` to `neg` (and conversely): turns the sign glyph of `b` into the
sign glyph of `-b`. -/
def asw_flipCmd : Cmd := seqs [.ite rB .pos (.set rB .neg) (.set rB .pos)]

/-- The sign-processing sub-program: flip the second sign for subtraction, keep it for addition. -/
def asw_fp (flip : Bool) : Cmd := cond flip asw_flipCmd .skip


/-- Parse the two integer values on stack 0: push the markers, split off the sign glyphs
(onto `sSgA`, `sSgB`; `fp` is applied to the second sign) and the magnitudes (onto `sA`,
`sB`, least significant digit first). -/
def asw_setup (fp : Cmd) : Cmd :=
  seqs [.set rA (gmk sBuf), .push sBuf rA,
    .set rA (gmk sA), .push sA rA,
    .set rA (gmk sB), .push sB rA,
    .set rA (gmk sO1), .push sO1 rA,
    .set rA (gmk sO2), .push sO2 rA,
    .set rA (gmk sSgA), .push sSgA rA,
    .set rA (gmk sSgB), .push sSgB rA,
    .pop 0 rB, .push sSgA rB,
    asw_drain 0 sBuf .iend rT rF,
    .pop 0 rT,
    asw_drain sBuf sA (gmk sBuf) rT rF,
    .pop 0 rB, fp, .push sSgB rB,
    asw_drain 0 sBuf .iend rT rF,
    .pop 0 rT,
    asw_drain sBuf sB (gmk sBuf) rT rF]

/-- Write an integer value with sign glyph on stack `sg` and magnitude digits on stack `out`
(most significant digit on top) on top of stack 0; a zero magnitude gets sign `pos`. -/
def asw_finish (sg out : Stk) : Cmd :=
  seqs [asw_stripLoop out,
    .set rS .iend, .push 0 rS,
    .pop sg rU,
    .peek out rT,
    .ite rT (gmk out) (.set rU .pos) .skip,
    asw_drain out 0 (gmk out) rA rF,
    .push 0 rU]

/-- Same-sign branch: add the magnitudes (carry initialised to `false`), sign unchanged; the
unused sign stack `sSgB` is popped so that both branches end with the same stack shape. -/
def asw_same : Cmd := seqs [.set rC (.bit false), .set rF gGo, asw_addLoop sA sB sO1,
  asw_finish sSgA sO1, .pop sSgB rU]

/-- Opposite-sign branch: subtract the magnitudes (both orders), pick the positive one
(its borrow is `false`) together with the sign of the larger operand; the unused output stack
and the unused sign stack are cleared/popped, so that both branches end with the same shape. -/
def asw_diff : Cmd := seqs [asw_subLoop sA sB sO1 sO2,
  .ite rC (.bit false)
    (seqs [asw_finish sSgA sO1, asw_clearAt sO2 (gmk sO2) rT rF, .pop sSgB rU])
    (seqs [asw_finish sSgB sO2, asw_clearAt sO1 (gmk sO1) rT rF, .pop sSgA rU])]

/-- Dispatch on whether the two sign glyphs agree. -/
def asw_dispatch : Cmd := seqs [.peek sSgA rA, .peek sSgB rB,
  .ite rA .pos (.ite rB .pos asw_same asw_diff) (.ite rB .pos asw_diff asw_same)]

/-- Restore all scratch stacks: pop everything down to the marker, then the marker. -/
def asw_cleanup : Cmd :=
  seqs [asw_clear sBuf (gmk sBuf) rT rF,
    asw_clear sA (gmk sA) rT rF,
    asw_clear sB (gmk sB) rT rF,
    asw_clear sO1 (gmk sO1) rT rF,
    asw_clear sO2 (gmk sO2) rT rF,
    asw_clear sSgA (gmk sSgA) rT rF,
    asw_clear sSgB (gmk sSgB) rT rF]

/-- The full program: `int a :: int b :: rest ↦ int (a + (if flip then -b else b)) :: rest`. -/
def asw_prog (flip : Bool) : Cmd :=
  seqs [asw_setup (asw_fp flip), asw_dispatch, asw_cleanup]

/-- A uniform cost bound: linear in the two digit-list lengths. -/
def asw_C (p q : ℕ) : ℕ := 400 * (p + q + 2) + 2000

theorem asw_C_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') : asw_C p q ≤ asw_C p' q' := by
  unfold asw_C; omega

theorem asw_C_ge_31 {p q : ℕ} : 31 * (p + q + 2) ≤ asw_C p q := by unfold asw_C; omega

/-- The cost of the output stage, whose input has at most `31 * (p+q+2)` digits. -/
theorem asw_C_bound_finish {p q l : ℕ} (h : l ≤ 31 * (p + q + 2)) : 5 * (l + 1) + 60 ≤ asw_C p q := by
  unfold asw_C; omega

/-- Idem for the clearing loop. -/
theorem asw_C_bound_clear {p q l : ℕ} (h : l ≤ 31 * (p + q + 2)) : 5 * (l + 1) + 10 ≤ asw_C p q := by
  unfold asw_C; omega

theorem asw_C_self {p q : ℕ} : asw_C p q ≤ 400 * (p + q + 2) + 2000 := le_rfl

end AddSub
end Work.IntLib
