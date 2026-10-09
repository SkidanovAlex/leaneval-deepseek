/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Places of `ℚ` and the finiteness of the set of places with `(a,b)_v ≠ 1`

For `a b : ℚˣ` the Hilbert symbol `(a,b)_v` is `1` at all places `v` except possibly the
archimedean place and the primes dividing `2 a b`.  This file packages that finite set of places
and the corresponding (finite) product of the Hilbert symbols.
-/
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.padicVal_eq_zero_iff
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- The natural number `|num a| * den a` attached to a nonzero rational `a = num/den`; primes
dividing it are exactly the primes at which `a` has nonzero `p`-adic valuation. -/
def numDenNat (a : ℚˣ) : ℕ := (a : ℚ).num.natAbs * (a : ℚ).den

/-- The finite set of finite places of `ℚ` at which the Hilbert symbol `(a,b)_v` can be
different from `1`: the prime `2` together with the prime divisors of the numerators and
denominators of `a` and `b`. -/
def contributingPrimes (a b : ℚˣ) : Finset ℕ :=
  insert 2 ((numDenNat a).primeFactors ∪ (numDenNat b).primeFactors)

theorem two_mem_contributingPrimes (a b : ℚˣ) : 2 ∈ contributingPrimes a b :=
  Finset.mem_insert_self 2 _

theorem mem_contributingPrimes {a b : ℚˣ} {p : ℕ} :
    p ∈ contributingPrimes a b ↔ p = 2 ∨ p ∈ (numDenNat a).primeFactors
      ∨ p ∈ (numDenNat b).primeFactors := by
  simp [contributingPrimes]

theorem numDenNat_primeUnit (p : ℕ) [Fact p.Prime] : numDenNat (primeUnit p) = p := by
  rw [numDenNat, primeUnit_coe, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast, mul_one]

theorem primeFactors_numDenNat_primeUnit (p : ℕ) [Fact p.Prime] :
    (numDenNat (primeUnit p)).primeFactors = {p} := by
  rw [numDenNat_primeUnit]
  exact Nat.Prime.primeFactors (Fact.out : p.Prime)

theorem contributingPrimes_comm (a b : ℚˣ) : contributingPrimes a b = contributingPrimes b a := by
  simp only [contributingPrimes, Finset.union_comm]

theorem numDenNat_one : numDenNat (1 : ℚˣ) = 1 := by
  simp [numDenNat]

theorem numDenNat_neg_one : numDenNat (-1 : ℚˣ) = 1 := by
  simp [numDenNat]

/-- The product of the Hilbert symbols `(a,b)_p` over the finite places `p` which can contribute
to the product formula for `(a,b)`. -/
def placeProd (a b : ℚˣ) : ℤˣ :=
  ∏ p ∈ contributingPrimes a b, hilbertSymbol (some p) a b

/-- The full product of the Hilbert symbols `(a,b)_v` over all places of `ℚ`.  It is a finite
product because only the places in `contributingPrimes a b` and the archimedean place can give a
contribution different from `1`. -/
def placeProduct (a b : ℚˣ) : ℤˣ :=
  placeProd a b * hilbertSymbol none a b

theorem placeProduct_def (a b : ℚˣ) :
    placeProduct a b =
      (∏ p ∈ contributingPrimes a b, hilbertSymbol (some p) a b) * hilbertSymbol none a b :=
  rfl

end Work.HilbertSymbol
