/-
# `Work.FIArea7.sum_sqfree_peel` — the *FI* (24.12) "peeling" of a squarefree sum

*Friedlander–Iwaniec* (24.12) split the sum over all squarefree `ℓ ⩽ X` into

* the part all of whose prime factors are `⩽ z` (this is `sepSumLHS`), and
* the rest, which is re-summed over the prime factors `p > z` of `ℓ`: each such `ℓ` is
  reached once for each of its `ν(ℓ) = #{r prime : z < r, r ∣ ℓ}` prime factors `> z`,
  and the inner sum is weighted by `1/ν(ℓ)`, so that every `ℓ` is counted exactly once.

The formal content is therefore a finite-sum reindexing: `peelSum` is a double sum over the
pairs `(p,q)`, `p` a prime `> z` with `p ⩽ X`, `q ⩽ X`, and the value `p·q = ℓ` is squarefree
and `⩽ X`.  Grouping those pairs by the value of `p·q`, each fibre over `ℓ` has exactly
`ν(ℓ)` elements (`card_fiber`), each contributing `f(ℓ)/ν(ℓ)`, so the whole sum is
`Σ_{ℓ ∈ peelIdx X z} f ℓ`.  Adding the small-prime part `sepSumLHS` recovers `sqfreeSum`.
-/
import Mathlib
import Submission.Work.FIArea7.SepDiv

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section
open Classical

/-- The primes `p` with `z < p ≤ X`.  This is exactly the index set of `peelSum`. -/
def largePrimes (X z : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (fun p => p.Prime ∧ z < p)

/-- `ν(l)`: the number of primes `r` with `z < r ≤ X` and `r ∣ l`.  This is the denominator
weight of `peelInner` (the paper's `ν(pq,z)`). -/
def largePrimeCount (X z l : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun r => r.Prime ∧ z < r ∧ r ∣ l)).card

/-- The squarefree `ℓ ⩽ X` that possess a prime factor `> z`: the "peeled" part of
`sqfreeSum`, i.e. the complement of the index set of `sepSumLHS`. -/
def peelIdx (X z : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 X).filter (fun l => Squarefree l)).filter
    (fun l => ¬ ∀ p, p.Prime → p ∣ l → p ≤ z)

/-- The pairs `(p,q)` over which `peelSum` runs: `p` a prime `> z` with `p ≤ X`, `q ≤ X`, and
the product `p·q` squarefree and `≤ X`. -/
def peelPairs (X z : ℕ) : Finset (ℕ × ℕ) :=
  ((largePrimes X z).product (Finset.Icc 1 X)).filter
    (fun pq => Squarefree (pq.1 * pq.2) ∧ pq.1 * pq.2 ≤ X)

/-- `ν(l)` counts the primes of `largePrimes` that divide `l`. -/
lemma largePrimeCount_eq_primes_filter (X z l : ℕ) :
    largePrimeCount X z l = ((largePrimes X z).filter (fun p => p ∣ l)).card := by
  unfold largePrimeCount largePrimes
  rw [Finset.filter_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- Every pair of `peelPairs` has a product lying in `peelIdx`. -/
lemma peelPairs_mapsTo (X z : ℕ) :
    ∀ pq ∈ peelPairs X z, pq.1 * pq.2 ∈ peelIdx X z := by
  intro pq hpq
  rw [peelPairs, Finset.mem_filter] at hpq
  obtain ⟨hprod, hsq, hle⟩ := hpq
  rw [Finset.product_eq_sprod, Finset.mem_product] at hprod
  obtain ⟨hp, hq⟩ := hprod
  obtain ⟨hp1X, hpprim, hzp⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1, hpX⟩ := Finset.mem_Icc.mp hp1X
  obtain ⟨hq1, hqX⟩ := Finset.mem_Icc.mp hq
  rw [peelIdx, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨⟨?_, hle⟩, hsq⟩, ?_⟩
  · have : 1 * 1 ≤ pq.1 * pq.2 := Nat.mul_le_mul hp1 hq1
    simpa using this
  · intro hcon
    have : pq.1 ≤ z := hcon pq.1 hpprim (Nat.dvd_mul_right pq.1 pq.2)
    omega

/-- The fibre of `peelPairs` over `l ∈ peelIdx X z` has exactly `ν(l)` elements: it is the
graph `p ↦ (p, l/p)` of the prime divisors `p ∈ largePrimes` of `l`. -/
lemma card_fiber (X z l : ℕ) (hl : l ∈ peelIdx X z) :
    ((peelPairs X z).filter (fun pq : ℕ × ℕ => pq.1 * pq.2 = l)).card
      = largePrimeCount X z l := by
  obtain ⟨hlmem, _⟩ := Finset.mem_filter.mp hl
  obtain ⟨hlIcc, hlsq⟩ := Finset.mem_filter.mp hlmem
  obtain ⟨hl1, hlX⟩ := Finset.mem_Icc.mp hlIcc
  rw [largePrimeCount_eq_primes_filter]
  symm
  refine Finset.card_bij
    (fun p (_ : p ∈ (largePrimes X z).filter (fun p => p ∣ l)) => (p, l / p)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hplarge, hpdvd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpIcc, hpprim, hzp⟩ := Finset.mem_filter.mp hplarge
    obtain ⟨hp1, hpX⟩ := Finset.mem_Icc.mp hpIcc
    have hppos : 0 < p := hpprim.pos
    have hple : p ≤ l := Nat.le_of_dvd (by omega) hpdvd
    have hmul : p * (l / p) = l := Nat.mul_div_cancel' hpdvd
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [peelPairs, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.product_eq_sprod, Finset.mem_product]
        refine ⟨hplarge, ?_⟩
        rw [Finset.mem_Icc]
        exact ⟨Nat.one_le_div_iff hppos |>.mpr hple,
          by have := Nat.div_le_self l p; omega⟩
      · have h1 : (p, l / p).1 * (p, l / p).2 = l := hmul
        rw [h1]
        exact ⟨hlsq, hlX⟩
    · exact hmul
  · intro p1 hp1 p2 hp2 heq
    exact congrArg Prod.fst heq
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbP, hbEq⟩ := hb
    rw [peelPairs, Finset.mem_filter] at hbP
    obtain ⟨hbprod, hbsq, hble⟩ := hbP
    rw [Finset.product_eq_sprod, Finset.mem_product] at hbprod
    obtain ⟨hb1L, hb2Q⟩ := hbprod
    obtain ⟨hb1Icc, hb1prim, hz1⟩ := Finset.mem_filter.mp hb1L
    have hb1pos : 0 < b.1 := hb1prim.pos
    refine ⟨b.1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨hb1L, ?_⟩
      rw [← hbEq]
      exact Nat.dvd_mul_right b.1 b.2
    · have hdiv : l / b.1 = b.2 := by
        rw [← hbEq]
        exact Nat.mul_div_cancel_left b.2 hb1pos
      exact Prod.ext rfl hdiv

/-- Every `l ∈ peelIdx` has a prime divisor `> z`, hence `ν(l) > 0`. -/
lemma largePrimeCount_pos (X z l : ℕ) (hl : l ∈ peelIdx X z) : 0 < largePrimeCount X z l := by
  obtain ⟨hlmem, hnl⟩ := Finset.mem_filter.mp hl
  obtain ⟨hlIcc, hlsq⟩ := Finset.mem_filter.mp hlmem
  obtain ⟨hl1, hlX⟩ := Finset.mem_Icc.mp hlIcc
  unfold largePrimeCount
  apply Finset.card_pos.mpr
  obtain ⟨p, hp⟩ := not_forall.mp hnl
  obtain ⟨hpprim, hp⟩ := Classical.not_imp.mp hp
  obtain ⟨hpdvd, hzp⟩ := Classical.not_imp.mp hp
  refine ⟨p, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hpprim.one_le, ?_⟩, hpprim, not_le.mp hzp, hpdvd⟩
  have hppos : 0 < p := hpprim.pos
  have hple : p ≤ l := Nat.le_of_dvd (by omega) hpdvd
  omega

/-- **The expansion of `peelSum`.**  Unfolding the two filters turns the double sum into a
sum over the pair set `peelPairs`, with the integrand `f(pq.1·pq.2) / ν(pq.1·pq.2)`. -/
lemma peelSum_eq_pairs (X z : ℕ) (f : ℕ → ℂ) :
    peelSum X z f
      = ∑ pq ∈ peelPairs X z, f (pq.1 * pq.2) / ((largePrimeCount X z (pq.1 * pq.2) : ℕ) : ℂ) := by
  simp only [peelSum, peelInner, largePrimes, largePrimeCount, peelPairs]
  conv_lhs => rw [← Finset.sum_product']
  conv_lhs => rw [← Finset.sum_filter]
  simp only [Finset.product_eq_sprod]

/-- **The peeling of `FI` (24.12).**  `peelSum` is the sum of `f` over exactly the squarefree
`ℓ ⩽ X` having a prime factor `> z`, i.e. over `peelIdx X z`. -/
lemma peelSum_eq (X z : ℕ) (f : ℕ → ℂ) :
    peelSum X z f = ∑ l ∈ peelIdx X z, f l := by
  rw [peelSum_eq_pairs]
  rw [← Finset.sum_fiberwise_of_maps_to' (peelPairs_mapsTo X z)
        (fun l => f l / ((largePrimeCount X z l : ℕ) : ℂ))]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_const, card_fiber X z l hl]
  have hne : ((largePrimeCount X z l : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (largePrimeCount_pos X z l hl))
  rw [nsmul_eq_mul, ← mul_div_assoc]
  exact mul_div_cancel_left₀ (f l) hne

/-- `sqfreeSum` splits into the `sepSumLHS` part (all prime factors `⩽ z`) and the `peelIdx`
part (a prime factor `> z`). -/
lemma sqfreeSum_split (X z : ℕ) (f : ℕ → ℂ) :
    sqfreeSum X f = sepSumLHS X z f + ∑ l ∈ peelIdx X z, f l := by
  have hA : sepSumLHS X z f
      = ∑ l ∈ ((Finset.Icc 1 X).filter (fun l => Squarefree l)).filter
          (fun l => ∀ p, p.Prime → p ∣ l → p ≤ z), f l := by
    rw [sepSumLHS, ← Finset.filter_filter]
  rw [sqfreeSum, peelIdx, hA]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **`FI` (24.12): peeling the large prime factors off the squarefree sum.**
`sqfreeSum` (all squarefree `ℓ ⩽ X`) equals the contribution of the squarefree `ℓ` all of
whose prime factors are `⩽ z` (`sepSumLHS`) plus the peeled contribution of the `ℓ` that own a
prime factor `> z` (`peelSum`). -/
theorem sum_sqfree_peel (X z : ℕ) (f : ℕ → ℂ) :
    sqfreeSum X f = sepSumLHS X z f + peelSum X z f := by
  rw [sqfreeSum_split X z f, peelSum_eq X z f]

end

end Work.FIArea7
