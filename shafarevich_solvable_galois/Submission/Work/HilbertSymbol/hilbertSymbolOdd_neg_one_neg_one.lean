import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- At every prime `p` the Hilbert symbol at the odd finite place attached to `-1` and `-1`
is trivial: `-1` is a `p`-adic unit, so both valuations vanish and the defining formula
reduces to `1`. -/
theorem hilbertSymbolOdd_neg_one_neg_one (p : ℕ) [Fact p.Prime] :
    hilbertSymbolOdd p (-1 : ℚˣ) (-1 : ℚˣ) = 1 := by
  apply hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
  · rw [show (-1 : ℚˣ) = -(1 : ℚˣ) by simp, padicVal_neg, padicVal_one]
  · rw [show (-1 : ℚˣ) = -(1 : ℚˣ) by simp, padicVal_neg, padicVal_one]

end Work.HilbertSymbol
