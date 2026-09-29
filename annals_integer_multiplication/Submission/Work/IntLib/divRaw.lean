import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.Kernel.Raw

/-!
# IntLib division: raw layer

Definitions shared by the long-division development (`Submission/Work/IntLib/divWord.lean`).

* `bitsG l` maps a `List Bool` to the corresponding list of `Glyph.bit`;
* `padBits n L` is the `L`-bit (least significant first) expansion of `n`;
* `mvRev`, `dropRgn`, `stripZeros`, `incBits`: raw stack-region procedures;
* `subBitVal`/`subBorrow`/`subBitProg`: one ripple-subtraction step;
* `subRippleBits`/`incBitsList`/`shiftBits`: the pure list-level functions those procedures
  compute;
* `coreSt`: the canonical state of the long-division core.

Stack layout of the core (markers `gP … gY`):

| stack | content |
|-------|---------|
| 0     | `z` (the caller's value stack below the two operands) |
| 1     | pending dividend bits (most significant first) |
| 2     | divisor, `L` bits, least significant first |
| 3     | remainder, `L` bits, least significant first |
| 4     | quotient bits (least significant first, possibly zero padded) |
| 5     | ripple-subtraction result accumulator |
| 6     | ripple-subtraction copy of the divisor |
| 7     | ripple-subtraction copy of the remainder |
| 8     | reversal / stripping scratch |
| 9     | `Y` (sign glyphs), used by the fix-ups |
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-! ## Markers and bit lists -/

abbrev gP : Glyph := .mk 1
abbrev gB : Glyph := .mk 2
abbrev gR : Glyph := .mk 3
abbrev gQ : Glyph := .mk 4
abbrev gS : Glyph := .mk 5
abbrev gC : Glyph := .mk 6
abbrev gD : Glyph := .mk 7
abbrev gX : Glyph := .mk 8
abbrev gY : Glyph := .mk 9

/-- The list of `Glyph.bit`s of a `List Bool`. -/
abbrev bitsG (l : List Bool) : List Glyph := l.map Glyph.bit

/-- The `L` low bits of `n`, least significant first. -/
def padBits (n L : ℕ) : List Bool := (List.range L).map fun i => n.testBit i

/-- The `L`-bit expansions of the two operands of a ripple subtraction. -/
def subBitVal (x y c : Bool) : Bool := ((x.toNat + 2 - y.toNat - c.toNat) % 2 == 1)
def subBorrow (x y c : Bool) : Bool := decide (y.toNat + c.toNat > x.toNat)

/-- Pure ripple subtraction of two equal-length bit lists (least significant first).  Returns the
final borrow and the result bits. -/
def subRippleBits : List Bool → List Bool → Bool → Bool × List Bool
  | [], [], c => (c, [])
  | x :: xs, y :: ys, c =>
    let r := subRippleBits xs ys (subBorrow x y c)
    (r.1, subBitVal x y c :: r.2)
  | _, _, c => (c, [])

/-- Increment of a bit list (least significant first). -/
def incBitsList : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: incBitsList xs

/-- Shift left by one and add the bit `d` on the low end, in a window of `L` bits. -/
def shiftBits (d : Bool) (L : ℕ) (r : List Bool) : List Bool := d :: r.take (L - 1)

/-! ## Raw region procedures -/

/-- Push the marker `T'` on stack `k'`, then move every glyph of stack `k` above its marker `T`
onto stack `k'` (above `T'`), reversing the order; finally drop `T`. -/
def mvRev (k : Stk) (T : Glyph) (k' : Stk) (T' : Glyph) (r : Reg) : Cmd :=
  .seq (.set r T') (.seq (.push k' r)
    (.seq (consume k T r (.push k' r)) (.pop k r)))

/-- Move every glyph of stack `k` above its marker `T` onto the top of stack `k'` (which must
already carry its own marker), reversing the order; finally drop `T`. -/
def mvRevOnto (k : Stk) (T : Glyph) (k' : Stk) (r : Reg) : Cmd :=
  .seq (consume k T r (.push k' r)) (.pop k r)

/-- Drop the region of stack `k` delimited by the marker `T`. -/
def dropRgn (k : Stk) (T : Glyph) (r : Reg) : Cmd := .seq (consume k T r .skip) (.pop k r)

/-- Drop the `Glyph.bit false` glyphs on top of the region of stack `k` (delimited by `T`), leaving
the first non-zero bit (or the marker) on top. -/
def stripZeros (k : Stk) (T : Glyph) (r : Reg) : Cmd :=
  .seq (.set r (Glyph.bit false))
    (.seq (.loop r (Glyph.bit false) (.pop k r))
      (.ite r .eos .skip (.push k r)))

/-- Loop body of `incBits`: look at the top bit of the region; if it is `true`, drop it and push a
`false` (carry) onto the scratch stack `S`; otherwise stop. -/
def incBitsLoopBody (k : Stk) (S : Stk) (rr rs : Reg) : Cmd :=
  .seq (.peek k rr)
    (.ite rr (Glyph.bit true)
      (.seq (.pop k rr) (.seq (.set rs (Glyph.bit false)) (.push S rs)))
      .skip)

/-- Final part of `incBits`: the first non-`true` bit has been peeked; push the carry and the
remaining high bits onto the scratch stack `S`. -/
def incBitsFinal (k : Stk) (T : Glyph) (S : Stk) (rr rs : Reg) : Cmd :=
  .ite rr (Glyph.bit false)
    (.seq (.pop k rr) (.seq (.set rs (Glyph.bit true)) (.seq (.push S rs)
      (.seq (consume k T rs (.push S rs)) (.pop k rs)))))
    (.seq (.pop k rr) (.seq (.set rs (Glyph.bit true)) (.push S rs)))

/-- Increment the (least significant first) bit region of stack `k` (delimited by `T`), using stack
`S` with marker `TS` as scratch; the result region is moved back onto `k`. -/
def incBits (k : Stk) (T : Glyph) (S : Stk) (TS : Glyph) (rr rs : Reg) : Cmd :=
  .seq (.set rr TS)
    (.seq (.push S rr)
      (.seq (.set rr (Glyph.bit true))
        (.seq (.loop rr (Glyph.bit true) (incBitsLoopBody k S rr rs))
          (.seq (incBitsFinal k T S rr rs) (mvRev S TS k T rs)))))

/-- One ripple-subtraction step: registers `rr`, `rb` hold the operand bits and `rc` the borrow;
updates `rc` to the new borrow and sets `rs` to the result bit. -/
def subBitProg (rr rb rc rs : Reg) : Cmd :=
  .ite rr (Glyph.bit true)
    (.ite rb (Glyph.bit true)
       (.ite rc (Glyph.bit true)
          (.seq (.set rs (Glyph.bit true)) (.set rc (Glyph.bit true)))
          (.seq (.set rs (Glyph.bit false)) (.set rc (Glyph.bit false))))
       (.ite rc (Glyph.bit true)
          (.seq (.set rs (Glyph.bit false)) (.set rc (Glyph.bit false)))
          (.seq (.set rs (Glyph.bit true)) (.set rc (Glyph.bit false)))))
    (.ite rb (Glyph.bit true)
       (.ite rc (Glyph.bit true)
          (.seq (.set rs (Glyph.bit false)) (.set rc (Glyph.bit true)))
          (.seq (.set rs (Glyph.bit true)) (.set rc (Glyph.bit true))))
       (.ite rc (Glyph.bit true)
          (.seq (.set rs (Glyph.bit true)) (.set rc (Glyph.bit true)))
          (.seq (.set rs (Glyph.bit false)) (.set rc (Glyph.bit false)))))

/-! ## Pure long-division arithmetic -/

/-- One step of binary long division: given the accumulated quotient `st.1` and remainder `st.2`
(`st.2 < bv`) and the next dividend bit `d`, returns the new `(quotient, remainder)`. -/
def dstep (bv : ℕ) (st : ℕ × ℕ) (d : Bool) : ℕ × ℕ :=
  let X := 2 * st.2 + d.toNat
  let qb := if bv ≤ X then 1 else 0
  (2 * st.1 + qb, X - qb * bv)

/-- Long division of the (most significant first) bit list `A` by `bv`. -/
def divFold (bv : ℕ) (A : List Bool) : ℕ × ℕ := A.foldl (dstep bv) (0, 0)

/-- Value of a (most significant first) bit list. -/
def bval (A : List Bool) : ℕ := A.foldl (fun acc b => 2 * acc + b.toNat) 0

/-! ## Iteration lemma with bounded step cost -/

/-- `Cmd.loop` unrolled along an explicit sequence of states, with only a *bound* on the cost of
each step: if the test register still holds `cc` at each `f i` (`i < n`) and one `body` run goes
from `f i` to `f (i+1)` in at most `c` steps, and the test fails at `f n`, then the loop reaches
`f n` in at most `n * (c + 1) + 1` steps. -/
theorem eval_loop_iterate_le (main : Cmd) (r : Reg) (cc : Glyph) (body : Cmd) (c : ℕ) :
    ∀ (n : ℕ) (f : ℕ → State),
      (∀ i < n, (f i).reg r = cc ∧ ∃ m, Eval main body (f i) (f (i + 1)) m ∧ m ≤ c) →
      (f n).reg r ≠ cc →
      ∃ m, Eval main (.loop r cc body) (f 0) (f n) m ∧ m ≤ n * (c + 1) + 1 := by
  intro n
  induction n with
  | zero =>
    intro f _ hstop
    exact ⟨1, Eval.loopF hstop, by simp⟩
  | succ n ih =>
    intro f hstep hstop
    obtain ⟨hreg0, m0, hev0, hm0⟩ := hstep 0 (Nat.zero_lt_succ n)
    obtain ⟨m', hev', hm'⟩ := ih (fun i => f (i + 1))
      (by intro i hi; exact hstep (i + 1) (by omega)) hstop
    refine ⟨m0 + m' + 1, Eval.loopT hreg0 hev0 hev', ?_⟩
    have : m' ≤ n * (c + 1) + 1 := hm'
    calc m0 + m' + 1 ≤ c + (n * (c + 1) + 1) + 1 := by omega
      _ = (n + 1) * (c + 1) + 1 := by ring

/-! ## Canonical state of the division core -/

/-- Canonical state of the division core: stack 0 holds `z`, stacks 1–9 hold the regions described
in the module docstring (the part below the markers is inherited from `b0`). -/
def coreSt (b0 : State) (z Y : List Glyph) (p b r q : List Bool) : State :=
  State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk b0 0 z) 1 (bitsG p ++ [gP])) 2 (bitsG b ++ [gB])) 3 (bitsG r ++ [gR])) 4 (bitsG q ++ [gQ])) 5 [gS]) 6 [gC]) 7 [gD]) 8 [gX]) 9 (Y ++ [gY])

abbrev rLoop : Reg := 1
abbrev rB_dv : Reg := 2
abbrev rC : Reg := 3
abbrev rS : Reg := 4
abbrev rT : Reg := 5
abbrev rU : Reg := 6
abbrev rV : Reg := 7

/-- `coreSt` with the loop register set. -/
def coreStR (b0 : State) (z Y : List Glyph) (p b r q : List Bool) (g : Glyph) : State :=
  (coreSt b0 z Y p b r q).updReg rLoop g

@[simp] theorem coreSt_stk0 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 0 = z := by simp [coreSt]

@[simp] theorem coreSt_stk1 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 1 = bitsG p ++ [gP] := by simp [coreSt]

@[simp] theorem coreSt_stk2 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 2 = bitsG b ++ [gB] := by simp [coreSt]

@[simp] theorem coreSt_stk3 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 3 = bitsG r ++ [gR] := by simp [coreSt]

@[simp] theorem coreSt_stk4 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 4 = bitsG q ++ [gQ] := by simp [coreSt]

@[simp] theorem coreSt_stk5 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 5 = [gS] := by simp [coreSt]

@[simp] theorem coreSt_stk6 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 6 = [gC] := by simp [coreSt]

@[simp] theorem coreSt_stk7 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 7 = [gD] := by simp [coreSt]

@[simp] theorem coreSt_stk8 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 8 = [gX] := by simp [coreSt]

@[simp] theorem coreSt_stk9 (b0 : State) (z Y : List Glyph) (p b r q : List Bool) :
    (coreSt b0 z Y p b r q).stk 9 = Y ++ [gY] := by simp [coreSt]

@[simp] theorem coreSt_stk_hi (b0 : State) (z Y : List Glyph) (p b r q : List Bool) (j : Stk)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h5 : j ≠ 5)
    (h6 : j ≠ 6) (h7 : j ≠ 7) (h8 : j ≠ 8) (h9 : j ≠ 9) :
    (coreSt b0 z Y p b r q).stk j = b0.stk j := by
  simp [coreSt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

@[simp] theorem coreStR_reg_loop (b0 : State) (z Y : List Glyph) (p b r q : List Bool) (g : Glyph) :
    (coreStR b0 z Y p b r q g).reg rLoop = g := by simp [coreStR]

@[simp] theorem coreStR_stk (b0 : State) (z Y : List Glyph) (p b r q : List Bool) (g : Glyph)
    (j : Stk) : (coreStR b0 z Y p b r q g).stk j = (coreSt b0 z Y p b r q).stk j := by
  simp [coreStR]

@[simp] theorem coreSt_reg (b0 : State) (z Y : List Glyph) (p b r q : List Bool) (r' : Reg) :
    (coreSt b0 z Y p b r q).reg r' = b0.reg r' := rfl

end Work.IntLib
