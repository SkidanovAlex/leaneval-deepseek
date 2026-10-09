import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.SmallLemmas
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_two_two
import Submission.Work.HilbertSymbol.hilbertSymbolReal_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- For the pair `(2, 2)` the set of contributing finite places is the singleton `{2}`:
`numDenNat (primeUnit 2) = 2` and `2` has only the prime divisor `2`. -/
lemma contributingPrimes_two_two : contributingPrimes (primeUnit 2) (primeUnit 2) = {2} := by
  rw [contributingPrimes, numDenNat_primeUnit,
    Nat.Prime.primeFactors (Fact.out : Nat.Prime 2)]
  simp

/-- **The product formula for `(2,2)`.** The product of the Hilbert symbols `(2,2)_v` over all
places `v` of `ℚ` equals `1`.  Only the finite place `2` and the archimedean place contribute: at
the finite place `2` the value is `hilbertSymbolTwo (primeUnit 2) (primeUnit 2) = 1`, and at the
archimedean place it is `1` because `2 > 0`. -/
theorem placeProduct_two_two : placeProduct (primeUnit 2) (primeUnit 2) = 1 := by
  rw [placeProduct_def, contributingPrimes_two_two, Finset.prod_singleton, hilbertSymbol_some,
    hilbertSymbolAtPrime_two, hilbertSymbolTwo_two_two, hilbertSymbol_none,
    hilbertSymbolReal_primeUnit, mul_one]

end Work.HilbertSymbol
