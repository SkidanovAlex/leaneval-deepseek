import Submission.Work.IntLib.SqrtGcd.Defs

/-!
# Ripple subtraction: pure layer

`subBit x y c` / `subBw x y c` are the result digit and the new borrow of the subtraction
`x - y - c` of three bits; `subDigits n as bs c` runs `n` such steps over the (least significant
first) bit lists `as`, `bs`, returning the final borrow and the digit list (least significant
first).  `padTo n l` pads `l` with zeros so that it has length `n`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

/-- The result digit of `x - y - c` (two's complement, i.e. `(x - y - c) % 2`). -/
def subBit (x y c : Bool) : Bool := ((x.toNat + 2 - y.toNat - c.toNat) % 2 == 1)

/-- The borrow out of `x - y - c`: `x - y - c < 0`. -/
def subBw (x y c : Bool) : Bool := decide (y.toNat + c.toNat > x.toNat)

theorem subBw_false_iff (x y c : Bool) : subBw x y c = false ↔ x.toNat ≥ y.toNat + c.toNat := by
  cases x <;> cases y <;> cases c <;> decide

/-- The digit identity: `x + 2·(borrow out) = y + c + digit`. -/
theorem subBw_subBit (x y c : Bool) :
    x.toNat + 2 * (subBw x y c).toNat = y.toNat + c.toNat + (subBit x y c).toNat := by
  cases x <;> cases y <;> cases c <;> decide

/-- `n` ripple subtraction steps, from the least significant bit first.  Returns the final borrow
and the digit list (least significant first). -/
def subDigits : ℕ → List Bool → List Bool → Bool → Bool × List Bool
  | 0, _, _, c => (c, [])
  | n + 1, as, bs, c =>
      let x := as.headD false
      let y := bs.headD false
      let r := subDigits n as.tail bs.tail (subBw x y c)
      (r.1, subBit x y c :: r.2)

/-- Pad `l` with zeros to length `n`. -/
def padTo (n : ℕ) (l : List Bool) : List Bool := l.take n ++ List.replicate (n - l.length) false

end SG
end Work.IntLib
