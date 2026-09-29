import Mathlib
import Submission.Work.IntLib.divPush

/-!
# IntLib division: list arithmetic for the ripple-subtraction loop

The ripple loop (`Work.IntLib.Div.rippleProg`) consumes the bit region of one stack while, for each
bit, rippling through the corresponding bit of another stack.  Its invariant is indexed by the
number `i` of bits already processed, and needs the following pure list identities:

* `take_succ_eq_concat_getD`: `A.take (i+1) = A.take i ++ [A.getD i false]` for `i < A.length`;
* `subRippleBits_take_succ`: the prefix relation for the ripple-subtraction function
  (`Div.subRippleBits_append` specialised to prefixes);
* `bitsG_drop_succ`, `bitsG_take_succ`, `bitsG_drop_length`: the corresponding statements for the
  glyph encoding `bitsG` of a bit list.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-- `take (i+1)` as `take i` followed by the `i`-th entry. -/
theorem take_succ_eq_concat_getD (A : List Bool) (i : ℕ) (hi : i < A.length) :
    A.take (i + 1) = A.take i ++ [A.getD i false] := by
  rw [← List.take_concat_get' A i hi, List.getD_eq_getElem A false hi]

/-- One more step of the ripple subtraction: the result bits accumulate on the left-to-right
(read: least significant first) order and the borrow carried into the next step is the outgoing
borrow of the prefix. -/
theorem subRippleBits_take_succ (A B : List Bool) (hAB : A.length = B.length) (i : ℕ)
    (hi : i < A.length) :
    subRippleBits (A.take (i + 1)) (B.take (i + 1)) false =
      (subBorrow (A.getD i false) (B.getD i false)
         (subRippleBits (A.take i) (B.take i) false).1,
       (subRippleBits (A.take i) (B.take i) false).2 ++
         [subBitVal (A.getD i false) (B.getD i false)
            (subRippleBits (A.take i) (B.take i) false).1]) := by
  have hB : i < B.length := by omega
  have hlen : (A.take i).length = (B.take i).length := by simp [hAB]
  rw [take_succ_eq_concat_getD A i hi, take_succ_eq_concat_getD B i hB,
    Div.subRippleBits_append (A.take i) (B.take i) (A.getD i false) (B.getD i false) false hlen]

/-- Dropping `i` glyphs of `bitsG A` exposes the `i`-th bit. -/
theorem bitsG_drop_succ (A : List Bool) (i : ℕ) (hi : i < A.length) :
    (bitsG A).drop i = Glyph.bit (A.getD i false) :: (bitsG A).drop (i + 1) := by
  have h : A.drop i = A.getD i false :: A.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem A false hi]
  rw [show (bitsG A).drop i = (A.drop i).map Glyph.bit from by simp [bitsG], h, List.map_cons,
    List.map_drop]

/-- Taking `i + 1` glyphs of `bitsG A` appends the `i`-th bit. -/
theorem bitsG_take_succ (A : List Bool) (i : ℕ) (hi : i < A.length) :
    bitsG (A.take (i + 1)) = bitsG (A.take i) ++ [Glyph.bit (A.getD i false)] := by
  rw [take_succ_eq_concat_getD A i hi]
  simp [bitsG]

/-- `bitsG A` has no glyphs beyond position `A.length`. -/
theorem bitsG_drop_length (A : List Bool) : (bitsG A).drop A.length = [] := by
  rw [show (bitsG A).drop A.length = (A.drop A.length).map Glyph.bit from by simp [bitsG],
    List.drop_length]
  rfl

/-- The region of length `i + 1` of `bitsG A` splits as the region of length `i` and the `i`-th
glyph (as a list, top of stack first). -/
theorem bitsG_take_rev_succ (A : List Bool) (i : ℕ) (hi : i < A.length) :
    (bitsG (A.take (i + 1))).reverse = Glyph.bit (A.getD i false) :: (bitsG (A.take i)).reverse := by
  rw [bitsG_take_succ A i hi]
  simp

/-! ## The state family of the ripple loop

The loop `consume stB gB rLoop (rippleBody stR)` consumes the bit region of stack `stB` (the region
is `bitsG A`, least significant bit on top) and, for each bit `A i`, ripples through the
corresponding bit `B i` of the region of `stR`, accumulating

* the bits of `B` (top first, i.e. reversed) on `stC`,
* the bits of `A` (top first) on `stD`,
* the result bits (top first) on `stS`,

and carrying the borrow in register `rgC`.  `ripSt` is the state after `i` completed steps: the
stacks `stB`, `stR`, `stC`, `stD`, `stS` and the registers `rgB`, `rgS`, `rgC`, `rLoop` are
updated, everything else is taken from the base state `b0`.  The loop register holds `eos` so that
the loop keeps going.

(`rgB` holds the last divisor bit the handler popped and `rgS` the last result bit it computed; at
`i = 0` they still hold their initial values, which is why the two helpers below dispatch on `i`.) -/

/-- The glyph in register `rgB` after `i` steps of the ripple loop. -/
def ripGB (b0 : State) (B : List Bool) : ℕ → Glyph
  | 0 => b0.reg Div.rgB
  | k + 1 => Glyph.bit (B.getD k false)

/-- The glyph in register `rgS` after `i` steps of the ripple loop. -/
def ripGS (b0 : State) (A B : List Bool) : ℕ → Glyph
  | 0 => b0.reg Div.rgS
  | k + 1 => Glyph.bit (subBitVal (A.getD k false) (B.getD k false)
      (subRippleBits (A.take k) (B.take k) false).1)

@[simp] theorem ripGB_zero (b0 : State) (B : List Bool) : ripGB b0 B 0 = b0.reg Div.rgB := rfl
@[simp] theorem ripGB_succ (b0 : State) (B : List Bool) (k : ℕ) :
    ripGB b0 B (k + 1) = Glyph.bit (B.getD k false) := rfl
@[simp] theorem ripGS_zero (b0 : State) (A B : List Bool) : ripGS b0 A B 0 = b0.reg Div.rgS := rfl
@[simp] theorem ripGS_succ (b0 : State) (A B : List Bool) (k : ℕ) :
    ripGS b0 A B (k + 1) = Glyph.bit (subBitVal (A.getD k false) (B.getD k false)
      (subRippleBits (A.take k) (B.take k) false).1) := rfl

/-- The state of the ripple loop after `i` completed steps.  `blB`, `blR`, `blC`, `blD`, `blS` are
the (unchanged) parts of the five participating stacks below the data the loop manipulates. -/
def ripSt (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) : State :=
  State.updReg (State.updReg (State.updReg (State.updReg
    (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk b0
      Div.stB ((bitsG A).drop i ++ [gB] ++ blB))
      Div.stR ((bitsG B).drop i ++ [gR] ++ blR))
      Div.stC ((bitsG (B.take i)).reverse ++ [gC] ++ blC))
      Div.stD ((bitsG (A.take i)).reverse ++ [gD] ++ blD))
      Div.stS ((bitsG ((subRippleBits (A.take i) (B.take i) false).2)).reverse ++ [gS] ++ blS))
    Div.rgB (ripGB b0 B i))
    Div.rgS (ripGS b0 A B i))
    Div.rgC (Glyph.bit ((subRippleBits (A.take i) (B.take i) false).1)))
    rLoop Glyph.eos

/-- The state sequence of the loop, extended by the terminal state reached after the marker of
`stB` has been popped (the loop test then fails because the loop register holds `mk 0`). -/
def ripFam (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) : State :=
  if i ≤ A.length then ripSt b0 blB blR blC blD blS A B i
  else (ripSt b0 blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0)

@[simp] theorem ripFam_of_le (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) (h : i ≤ A.length) :
    ripFam b0 blB blR blC blD blS A B i = ripSt b0 blB blR blC blD blS A B i := by
  simp [ripFam, h]

@[simp] theorem ripFam_of_gt (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) (h : ¬ i ≤ A.length) :
    ripFam b0 blB blR blC blD blS A B i =
      (ripSt b0 blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0) := by
  simp [ripFam, h]

@[simp] theorem ripSt_stB (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).stk Div.stB =
      (bitsG A).drop i ++ [gB] ++ blB := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_stR (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).stk Div.stR =
      (bitsG B).drop i ++ [gR] ++ blR := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_stC (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).stk Div.stC =
      (bitsG (B.take i)).reverse ++ [gC] ++ blC := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_stD (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).stk Div.stD =
      (bitsG (A.take i)).reverse ++ [gD] ++ blD := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_stS (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).stk Div.stS =
      (bitsG ((subRippleBits (A.take i) (B.take i) false).2)).reverse ++ [gS] ++ blS := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_stk_other (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) (j : Stk) (h1 : j ≠ Div.stB) (h2 : j ≠ Div.stR) (h3 : j ≠ Div.stC)
    (h4 : j ≠ Div.stD) (h5 : j ≠ Div.stS) :
    (ripSt b0 blB blR blC blD blS A B i).stk j = b0.stk j := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply,
    h1, h2, h3, h4, h5]

@[simp] theorem ripSt_reg_rgB (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).reg Div.rgB = ripGB b0 B i := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_reg_rgS (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).reg Div.rgS = ripGS b0 A B i := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_reg_rgC (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).reg Div.rgC =
      Glyph.bit ((subRippleBits (A.take i) (B.take i) false).1) := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_reg_rLoop (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) : (ripSt b0 blB blR blC blD blS A B i).reg rLoop = Glyph.eos := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem ripSt_reg_other (b0 : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) (r : Reg) (h1 : r ≠ Div.rgB) (h2 : r ≠ Div.rgS) (h3 : r ≠ Div.rgC)
    (h4 : r ≠ rLoop) :
    (ripSt b0 blB blR blC blD blS A B i).reg r = b0.reg r := by
  simp (config := { decide := true }) [ripSt, State.updStk, State.updReg, Function.update_apply,
    h1, h2, h3, h4]

end Work.IntLib
