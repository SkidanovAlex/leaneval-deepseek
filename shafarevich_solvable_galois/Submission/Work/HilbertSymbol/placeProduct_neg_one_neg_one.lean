import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_one_neg_one
import Submission.Work.HilbertSymbol.hilbertSymbolReal_neg_one_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The only finite place of `ℚ` that can contribute to the product formula for `(-1,-1)` is the
prime `2`: both entries are units at every odd prime. -/
theorem contributingPrimes_neg_one_neg_one :
    contributingPrimes (-1 : ℚˣ) (-1 : ℚˣ) = {2} := by
  simp [contributingPrimes, numDenNat]

/-- The place-product of `(-1,-1)` is `1`: at the only contributing finite place, `p = 2`, the
Hilbert symbol equals `-1`, and at the archimedean place it also equals `-1`, so the two signs
cancel. -/
theorem placeProduct_neg_one_neg_one : placeProduct (-1 : ℚˣ) (-1 : ℚˣ) = 1 := by
  rw [placeProduct_def, contributingPrimes_neg_one_neg_one]
  simp [hilbertSymbol_some, hilbertSymbolAtPrime_two, hilbertSymbolTwo_neg_one_neg_one,
    hilbertSymbol_none, hilbertSymbolReal_neg_one_neg_one]

end Work.HilbertSymbol
