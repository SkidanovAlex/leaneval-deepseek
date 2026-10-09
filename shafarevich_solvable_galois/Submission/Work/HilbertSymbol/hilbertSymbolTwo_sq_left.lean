import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_mul_left
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The `2`-adic Hilbert symbol vanishes on squares in its first argument.

Indeed `hilbertSymbolTwo` is multiplicative in the first argument
(`hilbertSymbolTwo_mul_left`), so `(a², b)_2 = (a, b)_2 * (a, b)_2 = 1`, because `ℤˣ` is a group
of exponent two (`Int.units_eq_one_or`). -/
theorem hilbertSymbolTwo_sq_left (a b : ℚˣ) : hilbertSymbolTwo (a ^ 2) b = 1 := by
  rw [pow_two, hilbertSymbolTwo_mul_left]
  rcases Int.units_eq_one_or (hilbertSymbolTwo a b) with h | h <;> rw [h] <;> decide

end Work.HilbertSymbol
