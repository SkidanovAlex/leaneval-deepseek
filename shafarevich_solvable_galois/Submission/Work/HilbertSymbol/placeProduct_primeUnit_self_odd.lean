import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.SmallLemmas
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_primeUnit_primeUnit_odd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self_odd
import Submission.Work.HilbertSymbol.hilbertSymbolReal_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-! ## The contributing primes of a pair of equal prime units

To keep this file self-contained we re-derive the elementary identification
`contributingPrimes (primeUnit p) (primeUnit p) = {2, p}` here (it only uses
`numDenNat` of a prime unit and the fact that the prime factors of `p` are `{p}`).
-/

private theorem numDenNat_primeUnit_eq (p : ℕ) [Fact p.Prime] :
    numDenNat (primeUnit p) = p := by
  rw [numDenNat, primeUnit_coe, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast, mul_one]

private theorem primeFactors_numDenNat_primeUnit_eq (p : ℕ) [Fact p.Prime] :
    (numDenNat (primeUnit p)).primeFactors = {p} := by
  rw [numDenNat_primeUnit_eq]
  exact Nat.Prime.primeFactors (Fact.out : p.Prime)

private theorem contributingPrimes_primeUnit_self {p : ℕ} [Fact p.Prime] :
    contributingPrimes (primeUnit p) (primeUnit p) = ({2, p} : Finset ℕ) := by
  rw [contributingPrimes, primeFactors_numDenNat_primeUnit_eq p, Finset.singleton_union]
  simp

/-- The product formula specialization `∏_v (p,p)_v = 1` for an odd prime `p`.

All three contributions are computed explicitly.  The only finite places that can contribute
are `2` and `p` itself, and the archimedean place gives `1`
(`hilbertSymbolReal_primeUnit`).  With `m = (p-1)/2`:

* `(p,p)_2 = (-1)^{m·m}` (the supplementary law at `2`, `hilbertSymbolTwo_primeUnit_primeUnit_odd`),
* `(p,p)_p = (-1)^m` (the supplementary law `(-1/p) = (-1)^m`,
  `hilbertSymbolOdd_primeUnit_self_odd`).

Since `m·m + m = m(m+1)` is even the product is `1`. -/
theorem placeProduct_primeUnit_self_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    placeProduct (primeUnit p) (primeUnit p) = 1 := by
  -- Only the places `2` and `p` can contribute, and they are distinct.
  have hcp : contributingPrimes (primeUnit p) (primeUnit p) = ({2, p} : Finset ℕ) :=
    contributingPrimes_primeUnit_self
  -- The two surviving local factors multiply to `(-1)^{m^2 + m} = 1`.
  have key : (-1 : ℤˣ) ^ ((((p - 1) / 2) * ((p - 1) / 2) : ℕ) : ℤ)
      * (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, zpow_natCast, ← pow_add]
    rw [show (p - 1) / 2 * ((p - 1) / 2) + (p - 1) / 2
        = (p - 1) / 2 * ((p - 1) / 2 + 1) by ring]
    exact Even.neg_one_pow (Nat.even_mul_succ_self ((p - 1) / 2))
  rw [placeProduct_def, hcp, Finset.prod_pair (Ne.symm hp), hilbertSymbol_some (p := 2),
    hilbertSymbol_some (p := p), hilbertSymbolAtPrime_two, hilbertSymbolAtPrime_eq_odd hp,
    hilbertSymbolTwo_primeUnit_primeUnit_odd hp hp, hilbertSymbolOdd_primeUnit_self_odd hp,
    intUnitOf_legendreSym_neg_one hp, hilbertSymbol_none, hilbertSymbolReal_primeUnit, mul_one]
  exact key

end Work.HilbertSymbol
