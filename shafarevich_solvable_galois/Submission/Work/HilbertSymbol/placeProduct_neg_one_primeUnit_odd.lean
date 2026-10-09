import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_one_primeUnit_odd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_neg_one_primeUnit
import Submission.Work.HilbertSymbol.hilbertSymbolReal_neg_one_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# The place product `∏_v (-1, p)_v` for an odd prime `p`

For an odd prime `p` the only places of `ℚ` at which the Hilbert symbol `(-1, p)_v` can differ
from `1` are `∞` and the two primes `2` and `p`, so

`∏_v (-1, p)_v = (-1, p)_2 · (-1, p)_p · (-1, p)_∞`.

The three factors are computed in the imported files:

* `(-1, p)_2 = (-1 / p)` (`hilbertSymbolTwo_neg_one_primeUnit_odd`),
* `(-1, p)_p = (-1 / p)` (`hilbertSymbolOdd_neg_one_primeUnit`),
* `(-1, p)_∞ = 1` (`hilbertSymbolReal_neg_one_primeUnit`).

The product is therefore `(-1/p)² = 1`, the global product formula in this special case.
-/

/-- Any value of `intUnitOf` is `±1`, hence squares to `1` in `ℤˣ`. -/
private theorem intUnitOf_mul_self (n : ℤ) : intUnitOf n * intUnitOf n = 1 := by
  rw [intUnitOf]; split_ifs <;> simp

/-- The only finite places of `ℚ` contributing to `(-1, p)` for an odd prime `p` are `2` and
`p`. -/
private theorem contributingPrimes_neg_one_primeUnit {p : ℕ} [Fact p.Prime] :
    contributingPrimes (-1 : ℚˣ) (primeUnit p) = insert 2 ({p} : Finset ℕ) := by
  rw [contributingPrimes, numDenNat_neg_one, numDenNat_primeUnit,
    Nat.Prime.primeFactors (Fact.out : p.Prime)]
  simp

theorem placeProduct_neg_one_primeUnit_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    placeProduct (-1 : ℚˣ) (primeUnit p) = 1 := by
  rw [placeProduct_def, contributingPrimes_neg_one_primeUnit,
    Finset.prod_insert (by simp [Ne.symm hp]), Finset.prod_singleton]
  simp only [hilbertSymbol_none]
  rw [hilbertSymbol_some, hilbertSymbolAtPrime_two, hilbertSymbol_some,
    hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolTwo_neg_one_primeUnit_odd hp,
    hilbertSymbolOdd_neg_one_primeUnit hp, hilbertSymbolReal_neg_one_primeUnit,
    intUnitOf_mul_self]
  simp

end Work.HilbertSymbol
