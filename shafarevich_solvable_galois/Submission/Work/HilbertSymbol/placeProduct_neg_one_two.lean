import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_one_two
import Submission.Work.HilbertSymbol.hilbertSymbolReal_neg_one_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# The product formula for `(-1, 2)`

We evaluate the full product of local Hilbert symbols

`∏_v (-1, 2)_v = 1`

for the rational numbers `-1` and `2`.

Since `numDenNat (-1) = numDenNat 1 = 1` and `numDenNat (primeUnit 2) = 2`, the only finite place
that can contribute is the prime `2`; hence `contributingPrimes (-1) (primeUnit 2) = {2}` and the
product reduces to the two symbols `(-1,2)_2` and `(-1,2)_∞`, both of which equal `1`:

* at the prime `2`, the exponent `ε(u)ε(v) + αω(v) + βω(u)` vanishes, because `-1` has valuation
  `0` and unit part `-1` (with `ε(-1) = 1`, `ω(-1) = 0`) while `2` has valuation `1` and unit part
  `1` (with `ε(1) = ω(1) = 0`);
* at the archimedean place, `(a,b)_∞ = -1` requires both `a` and `b` to be negative, but `2 > 0`.
-/

/-- The contributing primes of `(-1, primeUnit 2)` are exactly `{2}`. -/
theorem contributingPrimes_neg_one_two :
    contributingPrimes (-1 : ℚˣ) (primeUnit 2) = {2} := by
  rw [contributingPrimes, numDenNat_neg_one, numDenNat_primeUnit]
  norm_num

theorem placeProduct_neg_one_two : placeProduct (-1 : ℚˣ) (primeUnit 2) = 1 := by
  rw [placeProduct_def, contributingPrimes_neg_one_two, Finset.prod_singleton]
  rw [hilbertSymbol_some, hilbertSymbolAtPrime_two, hilbertSymbolTwo_neg_one_two,
    hilbertSymbol_none, hilbertSymbolReal_neg_one_primeUnit, mul_one]

end Work.HilbertSymbol
