/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicativity of `placeProduct` in the second argument

The full product `placeProduct a b = ∏_v (a,b)_v` of the Hilbert symbols over all places of `ℚ`
is multiplicative in the second argument:
`placeProduct a (b₁ * b₂) = placeProduct a b₁ * placeProduct a b₂`.

The mathematical content is that

* the archimedean factor `(a,b)_∞` is multiplicative in `b`, and
* the finite product over `contributingPrimes a b` is multiplicative in `b`, because the
  Hilbert symbol `(a,b)_p` is multiplicative in `b` at every prime `p` and is trivial at every
  prime outside `contributingPrimes a b`.  The latter lets us replace the three different index
  sets `contributingPrimes a bᵢ` by their union `S` and then multiply termwise.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace Work.HilbertSymbol

/-- `numDenNat a` is a nonzero natural number, so its `primeFactors` describe divisibility. -/
private theorem numDenNat_ne_zero (a : ℚˣ) : numDenNat a ≠ 0 := by
  rw [numDenNat]
  exact mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr a.ne_zero)) (Rat.den_nz _)

/-- The Hilbert symbol `(a,b)_p` is trivial at every finite place `p` outside
`contributingPrimes a b`.  For a prime `p` this is because then `v_p a = v_p b = 0`, and for a
non-prime `p` it holds by definition. -/
private theorem hilbertSymbol_some_eq_one_of_not_mem_contributingPrimes {a b : ℚˣ} {p : ℕ}
    (hp : p ∉ contributingPrimes a b) : hilbertSymbol (some p) a b = 1 := by
  rw [mem_contributingPrimes] at hp
  simp only [not_or] at hp
  obtain ⟨hp2, hpa, hpb⟩ := hp
  by_cases hpprime : p.Prime
  · haveI : Fact p.Prime := ⟨hpprime⟩
    -- For a prime `p` outside `contributingPrimes a b` the reduction of `a` and `b` is a unit,
    -- i.e. `p` does not divide the numerator or the denominator of either rational.
    have key : ∀ c : ℚˣ, p ∉ (numDenNat c).primeFactors → padicVal p c = 0 := by
      intro c hc
      have hndvd : ¬ p ∣ numDenNat c := fun h =>
        hc (Nat.mem_primeFactors.mpr ⟨hpprime, h, numDenNat_ne_zero c⟩)
      rw [padicVal_eq_zero_iff]
      constructor
      · intro hdiv
        apply hndvd
        have h' := Int.natAbs_dvd_natAbs.mpr hdiv
        rw [Int.natAbs_natCast] at h'
        change p ∣ (c : ℚ).num.natAbs * (c : ℚ).den
        exact dvd_mul_of_dvd_left h' _
      · intro hdiv
        apply hndvd
        change p ∣ (c : ℚ).num.natAbs * (c : ℚ).den
        exact dvd_mul_of_dvd_right hdiv _
    rw [hilbertSymbol_some, hilbertSymbolAtPrime_eq_odd hp2]
    exact hilbertSymbolOdd_eq_one_of_padicVal_eq_zero (key a hpa) (key b hpb)
  · simp only [hilbertSymbol, dif_neg hpprime]

/-- The finite product `∏_{p ∈ contributingPrimes a b} (a,b)_p` may be extended to any larger
finite set `S` of places, since the extra factors are trivial. -/
private theorem prod_contributingPrimes_eq_prod_of_subset {a b : ℚˣ} {S : Finset ℕ}
    (hS : contributingPrimes a b ⊆ S) :
    (∏ p ∈ contributingPrimes a b, hilbertSymbol (some p) a b)
      = ∏ p ∈ S, hilbertSymbol (some p) a b :=
  Finset.prod_subset hS
    (fun _ _ hx => hilbertSymbol_some_eq_one_of_not_mem_contributingPrimes hx)

theorem placeProduct_mul_right (a b₁ b₂ : ℚˣ) :
    placeProduct a (b₁ * b₂) = placeProduct a b₁ * placeProduct a b₂ := by
  -- A common finite set of places containing all three contributing sets.
  set S := contributingPrimes a (b₁ * b₂) ∪ (contributingPrimes a b₁ ∪ contributingPrimes a b₂)
  have hX : (∏ p ∈ contributingPrimes a (b₁ * b₂), hilbertSymbol (some p) a (b₁ * b₂))
      = ∏ p ∈ S, hilbertSymbol (some p) a (b₁ * b₂) :=
    prod_contributingPrimes_eq_prod_of_subset (fun _ hx => Finset.mem_union_left _ hx)
  have hY : (∏ p ∈ contributingPrimes a b₁, hilbertSymbol (some p) a b₁)
      = ∏ p ∈ S, hilbertSymbol (some p) a b₁ :=
    prod_contributingPrimes_eq_prod_of_subset (fun _ hx => Finset.mem_union_right _ (Finset.mem_union_left _ hx))
  have hZ : (∏ p ∈ contributingPrimes a b₂, hilbertSymbol (some p) a b₂)
      = ∏ p ∈ S, hilbertSymbol (some p) a b₂ :=
    prod_contributingPrimes_eq_prod_of_subset (fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx))
  -- The finite product over the common set splits, using multiplicativity in `b` at each place.
  have hprod : (∏ p ∈ S, hilbertSymbol (some p) a (b₁ * b₂))
      = (∏ p ∈ S, hilbertSymbol (some p) a b₁) * (∏ p ∈ S, hilbertSymbol (some p) a b₂) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun p _ => hilbertSymbol_mul_right (some p) a b₁ b₂)
  rw [placeProduct_def, placeProduct_def, placeProduct_def, hX, hY, hZ, hprod,
    hilbertSymbol_mul_right]
  ac_rfl

end Work.HilbertSymbol
