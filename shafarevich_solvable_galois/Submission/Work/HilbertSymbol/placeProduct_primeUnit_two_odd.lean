/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The product formula for `(p, 2)` with `p` an odd prime

For an odd prime `p` the product of the Hilbert symbols `(p, 2)_v` over **all** places `v` of `ℚ`
equals `1`:
`placeProduct (primeUnit p) (primeUnit 2) = 1`.

The two finite places that contribute are `2` and `p`, and at both of them the symbol equals the
Legendre symbol `(2/p)`:

* `(p, 2)_2 = (2/p)` at the place `2`, and
* `(p, 2)_p = (2/p)` at the place `p`,

while the archimedean symbol is `1` because both arguments are positive.  Since `(2/p) = ±1`,
the two contributions multiply to `1`, which is the product formula in this special case.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.SmallLemmas
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_primeUnit_two_odd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_two_odd
import Submission.Work.HilbertSymbol.hilbertSymbolReal_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- The prime divisors of `numDenNat (primeUnit p)` are exactly `p`. -/
theorem primeFactors_numDenNat_primeUnit_aux (p : ℕ) [Fact p.Prime] :
    (numDenNat (primeUnit p)).primeFactors = {p} := by
  rw [numDenNat_primeUnit]
  exact Nat.Prime.primeFactors (Fact.out : p.Prime)

/-- For a pair of primes `p`, `q` the contributing primes are exactly `2`, `p` and `q`: the only
finite places at which `(p, q)_v` can be non-trivial. -/
theorem contributingPrimes_primeUnit_aux {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    contributingPrimes (primeUnit p) (primeUnit q) = insert 2 ({p, q} : Finset ℕ) := by
  rw [contributingPrimes, primeFactors_numDenNat_primeUnit_aux p,
    primeFactors_numDenNat_primeUnit_aux q]
  simp [Finset.singleton_union]

theorem placeProduct_primeUnit_two_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    placeProduct (primeUnit p) (primeUnit 2) = 1 := by
  -- The only contributing finite places are `2` and `p`.
  have hset : contributingPrimes (primeUnit p) (primeUnit 2) = ({2, p} : Finset ℕ) := by
    rw [contributingPrimes_primeUnit_aux (p := p) (q := 2)]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- The symbol at the place `2` is `(2/p)`.
  have h2 : hilbertSymbol (some 2) (primeUnit p) (primeUnit 2)
      = intUnitOf (legendreSym p 2) := by
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_two, hilbertSymbolTwo_primeUnit_two_odd hp]
  -- The symbol at the place `p` is also `(2/p)`.
  have hpp : hilbertSymbol (some p) (primeUnit p) (primeUnit 2)
      = intUnitOf (legendreSym p 2) := by
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_primeUnit_two_odd hp]
  -- The archimedean symbol is trivial since both arguments are positive.
  have hr : hilbertSymbol none (primeUnit p) (primeUnit 2) = 1 := hilbertSymbolReal_primeUnit
  -- `(2/p) = ±1`, so its square is `1`.
  have hu : intUnitOf (legendreSym p 2) * intUnitOf (legendreSym p 2) = 1 := by
    by_cases h : legendreSym p 2 = -1
    · simp [intUnitOf, h]
    · simp [intUnitOf, h]
  -- `{2, p} = insert 2 {p}` because `p ≠ 2`.
  have hset' : ({2, p} : Finset ℕ) = insert 2 ({p} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [placeProduct_def, hset, hset',
    Finset.prod_insert (by simp only [Finset.mem_singleton]; exact fun h => hp h.symm),
    Finset.prod_singleton, h2, hpp, hr, hu]
  simp

end Work.HilbertSymbol
