import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.divRaw
import Submission.Work.Layout.Base

/-!
# Sqrt / gcd words: shared conventions

This area implements the two words `HvdH.IntLib.sqrt` and `HvdH.IntLib.gcd` of
`Submission/HvdH/Interfaces.lean`:

* `int a :: rest ↦ int (Nat.sqrt a.toNat) :: rest` when `0 ≤ a`, at cost `O(isz a ^ 2)`;
* `int a :: int b :: rest ↦ int (Int.gcd a b) :: rest`, at cost `O((isz a + isz b) ^ 2)`.

Everything is done with raw *bit regions* on the scratch stacks `1..7`.  A region on stack `k`
is delimited by the marker `Glyph.mk k` sitting at the bottom of our data; the data above it is
a list of `Glyph.bit`s, read **from the top**: popping gives the region "least significant bit
first".
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

/-! ## Stacks, registers, glyphs -/

def sA : Stk := 1
def sB : Stk := 2
def sC : Stk := 3
def sP : Stk := 4
def sQ : Stk := 5
def sR : Stk := 6
def sS : Stk := 7

def rgT : Reg := 0
def rgX : Reg := 1
def rgY : Reg := 2
def rgZ : Reg := 3
def rgC : Reg := 4
def rgF : Reg := 5

/-- loop-continue flag -/
def gGo : Glyph := .mk 8
/-- loop-stop flag -/
def gStop : Glyph := .mk 9
/-- comparison result: less -/
def gLt : Glyph := .mk 10
/-- comparison result: equal -/
def gEq : Glyph := .mk 11
/-- comparison result: greater -/
def gGt : Glyph := .mk 12
/-- unary counter tick -/
def gTick : Glyph := .mk 13
/-- the marker of stack `k` -/
abbrev mkG (k : Stk) : Glyph := .mk k

/-! ## Bit lists

`List Bool` is always *least significant bit first* (`Nat.bits` order); a *most significant
first* list is the reverse of such a list. -/

/-- Value of a *most significant first* bit list. -/
def bval (g : List Bool) : ℕ := ofBits g.reverse

theorem bval_nil : bval [] = 0 := rfl

theorem bval_append (g h : List Bool) : bval (g ++ h) = bval h + 2 ^ h.length * bval g := by
  simp only [bval, List.reverse_append, ofBits_append, List.length_reverse]

theorem bval_lt (g : List Bool) : bval g < 2 ^ g.length := by
  simpa [bval] using ofBits_lt_two_pow g.reverse

theorem bval_cons (b : Bool) (g : List Bool) : bval (b :: g) = bval g + 2 ^ g.length * b.toNat := by
  have h := bval_append [b] g
  simpa [bval, ofBits] using h

theorem bval_singleton (b : Bool) : bval [b] = b.toNat := by simp [bval, ofBits]

theorem bval_pair (x y : Bool) : bval [x, y] = 2 * x.toNat + y.toNat := by
  cases x <;> cases y <;> decide

/-- Appending a pair to a *most significant first* list: the pair is the low-order part. -/
theorem bval_append_pair (pre : List Bool) (x y : Bool) :
    bval (pre ++ [x, y]) = 4 * bval pre + (2 * x.toNat + y.toNat) := by
  rw [bval_append, bval_pair]; simp; ring

/-- Splitting a *most significant first* list into a processed prefix and the rest. -/
theorem bval_take_drop (g : List Bool) (i : ℕ) :
    bval g = bval (g.drop i) + 2 ^ (g.drop i).length * bval (g.take i) := by
  conv_lhs => rw [← List.take_append_drop i g]
  rw [bval_append]

/-- Two leading bits followed by the rest. -/
theorem bval_cons_cons (x y : Bool) (r : List Bool) :
    bval (x :: y :: r) = bval r + 2 ^ r.length * (2 * x.toNat + y.toNat) := by
  rw [show (x :: y :: r) = [x, y] ++ r from rfl, bval_append, bval_pair]

/-- Value of a *least significant first* list, for short. -/
abbrev lval (g : List Bool) : ℕ := ofBits g

theorem lval_append (g h : List Bool) : lval (g ++ h) = lval g + 2 ^ g.length * lval h :=
  ofBits_append g h

end SG
end Work.IntLib
