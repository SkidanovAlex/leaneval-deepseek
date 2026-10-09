/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The product formula for the Hilbert symbol of two distinct odd primes

For distinct odd primes `p` and `q`, the product of the Hilbert symbols `(p,q)_v` over *all*
places `v` of `ℚ` equals `1`.

Only four places can contribute:

* `v = ∞`: the symbol is `1` because `p, q > 0` (`hilbertSymbolReal_primeUnit`);
* `v = 2`: the symbol is `(-1) ^ ((p-1)/2 * (q-1)/2)` (`hilbertSymbolTwo_primeUnit_primeUnit_odd`);
* `v = p`: the symbol is the Legendre symbol `(q/p)` (`hilbertSymbolOdd_primeUnit_of_ne`);
* `v = q`: the symbol is the Legendre symbol `(p/q)` (the same computation with `p` and `q`
  exchanged, using the commutativity of the Hilbert symbol at a finite place).

The two Legendre symbols multiply to `(-1) ^ ((p-1)/2 * (q-1)/2)` by quadratic reciprocity
(`legendreSym_quadratic_reciprocity`), which cancels the contribution of the place `2`.  This is
the simplest non-degenerate case of the product formula for the Hilbert symbol.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.SmallLemmas
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_primeUnit_primeUnit_odd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_of_ne
import Submission.Work.HilbertSymbol.hilbertSymbolReal_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- `numDenNat` of a prime unit `p` is `p` itself. -/
private theorem numDenNat_primeUnit_local (p : ℕ) [Fact p.Prime] : numDenNat (primeUnit p) = p := by
  simp [numDenNat, primeUnit, ratUnit]

/-- The prime divisors of `numDenNat (primeUnit p)` are exactly `p`. -/
private theorem primeFactors_numDenNat_primeUnit_local (p : ℕ) [Fact p.Prime] :
    (numDenNat (primeUnit p)).primeFactors = {p} := by
  rw [numDenNat_primeUnit_local p]
  exact Nat.Prime.primeFactors (Fact.out : p.Prime)

/-- The contributing primes of a pair of prime units `p`, `q` are `2`, `p` and `q`. -/
private theorem contributingPrimes_primeUnit_local {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    contributingPrimes (primeUnit p) (primeUnit q) = insert 2 ({p, q} : Finset ℕ) := by
  rw [contributingPrimes, primeFactors_numDenNat_primeUnit_local p,
    primeFactors_numDenNat_primeUnit_local q]
  simp [Finset.singleton_union]

/-- `(-1) ^ m` is its own inverse in any monoid with a distributive negation. -/
private theorem neg_one_pow_mul_self (m : ℕ) :
    (-1 : ℤˣ) ^ m * (-1 : ℤˣ) ^ m = 1 := by
  rw [← pow_two, ← pow_mul, show m * 2 = 2 * m by ring, pow_mul]
  norm_num

theorem placeProduct_primeUnit_primeUnit_distinct_odd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    placeProduct (primeUnit p) (primeUnit q) = 1 := by
  have hp2 : (2 : ℕ) ≠ p := fun h => hp h.symm
  have hq2 : (2 : ℕ) ≠ q := fun h => hq h.symm
  have h2not : (2 : ℕ) ∉ ({p, q} : Finset ℕ) := by simp [hp2, hq2]
  have hpnot : p ∉ ({q} : Finset ℕ) := by simp [hpq]
  -- The place `2`.
  have h2 : hilbertSymbol (some 2) (primeUnit p) (primeUnit q)
      = (-1 : ℤˣ) ^ ((((p - 1) / 2 : ℕ) * ((q - 1) / 2 : ℕ) : ℕ) : ℤ) := by
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_two,
      hilbertSymbolTwo_primeUnit_primeUnit_odd hp hq]
  -- The place `p`.
  have hp' : hilbertSymbol (some p) (primeUnit p) (primeUnit q)
      = intUnitOf (legendreSym p q) := by
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_eq_odd hp]
    exact hilbertSymbolOdd_primeUnit_of_ne hpq
  -- The place `q` (commute the arguments to apply the `p`-version with `p` and `q` swapped).
  have hq' : hilbertSymbol (some q) (primeUnit p) (primeUnit q)
      = intUnitOf (legendreSym q p) := by
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_eq_odd hq, hilbertSymbolOdd_comm]
    exact hilbertSymbolOdd_primeUnit_of_ne hpq.symm
  rw [placeProduct_def, contributingPrimes_primeUnit_local, Finset.prod_insert h2not,
    Finset.prod_insert hpnot, Finset.prod_singleton, h2, hp', hq', hilbertSymbol_none,
    hilbertSymbolReal_primeUnit]
  -- Quadratic reciprocity cancels the contribution of the place `2`.
  rw [intUnitOf_legendreSym_mul hpq, legendreSym_quadratic_reciprocity hp hq hpq,
    intUnitOf_neg_one_pow, mul_one, zpow_natCast]
  exact neg_one_pow_mul_self _

end Work.HilbertSymbol
