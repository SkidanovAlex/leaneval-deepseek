import Mathlib
import Submission.Work.LinnikBurgess.singleton_ssa_defs

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-!
## Divisor bounds for the "high" primes of `q`

`highPrimeSet q` is the set of primes `p` with `2 ≤ q.factorization p`.  This file collects the
elementary bounds on the divisor function `q.divisors.card` and on the product of the high prime
powers that are needed by the U13 assembly:

* the product `∏_{p ∈ highPrimeSet q} (e_p + 1)` is at most `q.divisors.card`;
* the product `∏_{p ∈ highPrimeSet q} p ^{e_p}` divides `q`, hence is at most `q`, which gives
  `∏_{p ∈ highPrimeSet q} p^{e_p/6} ≤ q^{1/6}`;
* `2 ^ #(highPrimeSet q)` and `3 ^ #(highPrimeSet q)` are at most `q.divisors.card`.
-/

/-- If the exponent of `p` in `q` is nonzero then `p` is a prime factor of `q`. -/
lemma mem_primeFactors_of_factorization_ne_zero {q p : ℕ} (h : q.factorization p ≠ 0) :
    p ∈ q.primeFactors := by
  rw [← Nat.support_factorization]
  exact Finsupp.mem_support_iff.mpr h

lemma mem_highPrimeSet_iff {q p : ℕ} (hp : p ∈ q.primeFactors) :
    p ∈ highPrimeSet q ↔ 2 ≤ q.factorization p := by
  rw [highPrimeSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- Every prime factor occurs with positive exponent. -/
lemma one_le_factorization_of_mem_primeFactors {q p : ℕ} (hp : p ∈ q.primeFactors) :
    1 ≤ q.factorization p := by
  have h : q.factorization p ≠ 0 := by
    rw [← Nat.support_factorization] at hp
    exact Finsupp.mem_support_iff.mp hp
  omega

lemma highPrimeSet_subset (q : ℕ) : highPrimeSet q ⊆ q.primeFactors := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- A product over the subtype `↥s` is a product over `s`. -/
lemma prod_subtype_eq {s : Finset ℕ} {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ p : ↥s, f p.val) = ∏ p ∈ s, f p :=
  Finset.prod_coe_sort s f

/-- `rpow` version of `Finset.prod_pow` for products over a subtype. -/
lemma prod_subtype_rpow {s : Finset ℕ} (f : ℕ → ℝ) (hf : ∀ p ∈ s, 0 ≤ f p) (r : ℝ) :
    (∏ p : ↥s, f p.val ^ r) = (∏ p : ↥s, f p.val) ^ r := by
  rw [prod_subtype_eq (s := s) (fun p => f p ^ r), prod_subtype_eq (s := s) f]
  exact Real.finsetProd_rpow s f hf r

/-- The product over the high primes of the local divisor factors `e_p + 1` is a sub-product of
the full divisor count `∏_{p | q}(e_p + 1) = q.divisors.card`. -/
lemma high_prod_divisors_bound {q : ℕ} (hq : 0 < q) :
    (∏ p ∈ highPrimeSet q, (q.factorization p + 1)) ≤ q.divisors.card := by
  have hqne : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  rw [Nat.card_divisors hqne]
  refine Finset.prod_le_prod_of_subset_of_one_le₀ (highPrimeSet_subset q)
    (fun i _ => Nat.zero_le _) ?_
  intro i hi _
  have h := one_le_factorization_of_mem_primeFactors hi
  omega

/-- The product of the high prime powers of `q` divides `q`. -/
lemma high_prod_pow_dvd {q : ℕ} (hq : 0 < q) :
    (∏ p ∈ highPrimeSet q, p ^ q.factorization p) ∣ q := by
  have hqne : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hqne]
  exact Finset.prod_dvd_prod_of_subset (highPrimeSet q) (q.primeFactors)
    (fun p => p ^ q.factorization p) (highPrimeSet_subset q)

/-- The product over the high primes is at most `q`. -/
lemma high_prod_pow_le {q : ℕ} (hq : 0 < q) :
    (∏ p ∈ highPrimeSet q, p ^ q.factorization p) ≤ q :=
  Nat.le_of_dvd hq (high_prod_pow_dvd hq)

theorem divisor_bounds_high {q : ℕ} (hq : 0 < q) {d : ℕ}
    (hd : d.primeFactors.card ≤ (highPrimeSet q).card) :
    (2 : ℝ) ^ (highPrimeSet q).card ≤ (q.divisors.card : ℝ)
      ∧ (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
          ≤ (q.divisors.card : ℝ) ^ 2
      ∧ (∏ p : ↥(highPrimeSet q), (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6))
          ≤ (q : ℝ) ^ ((1 : ℝ) / 6)
      ∧ (3 : ℝ) ^ d.primeFactors.card ≤ (q.divisors.card : ℝ) ^ 2 := by
  have hmain := high_prod_divisors_bound hq
  have hdiv := high_prod_pow_dvd hq
  -- `2 ^ #H ≤ τ(q)` and `3 ^ #H ≤ τ(q)`
  have hpow_le : ∀ b : ℕ, b ≤ 3 → b ^ (highPrimeSet q).card ≤ q.divisors.card := by
    intro b hb
    have hp : (∏ _p ∈ highPrimeSet q, b) = b ^ (highPrimeSet q).card := by
      rw [Finset.prod_const]
    rw [← hp]
    refine le_trans (Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) ?_) hmain
    intro i hi
    have h2 : 2 ≤ q.factorization i := (Finset.mem_filter.mp hi).2
    omega
  have h2H : 2 ^ (highPrimeSet q).card ≤ q.divisors.card := hpow_le 2 (by norm_num)
  have hHle : (∏ p ∈ highPrimeSet q, p ^ q.factorization p) ≤ q := high_prod_pow_le hq
  -- the real-valued identities
  have hinner : (∏ p : ↥(highPrimeSet q), (p.val : ℝ) ^ ((q.factorization p.val : ℝ)))
      = ((∏ p ∈ highPrimeSet q, p ^ q.factorization p : ℕ) : ℝ) := by
    rw [prod_subtype_eq (s := highPrimeSet q)
      (f := fun p => (p : ℝ) ^ ((q.factorization p : ℕ) : ℝ)), Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [Nat.cast_pow, Real.rpow_natCast]
  have hlog : (∏ p : ↥(highPrimeSet q), (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6))
      = ((∏ p ∈ highPrimeSet q, p ^ q.factorization p : ℕ) : ℝ) ^ ((1 : ℝ) / 6) := by
    have hstep : ∀ p : ↥(highPrimeSet q),
        (p.val : ℝ) ^ ((q.factorization p.val : ℝ) / 6)
          = ((p.val : ℝ) ^ ((q.factorization p.val : ℕ) : ℝ)) ^ ((1 : ℝ) / 6) := by
      intro p
      rw [← Real.rpow_mul (show (0 : ℝ) ≤ (p.val : ℝ) by positivity)]
      congr 1
      ring
    simp only [hstep]
    rw [prod_subtype_rpow (s := highPrimeSet q)
      (f := fun p => (p : ℝ) ^ ((q.factorization p : ℕ) : ℝ))
      (fun p _ => by positivity) ((1 : ℝ) / 6), hinner]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast h2H
  · have hprod : (∏ p : ↥(highPrimeSet q), ((q.factorization p.val + 1 : ℕ) : ℝ) ^ 2)
        = ((∏ p ∈ highPrimeSet q, (q.factorization p + 1) : ℕ) : ℝ) ^ 2 := by
      rw [prod_subtype_eq (s := highPrimeSet q)
            (f := fun p => ((q.factorization p + 1 : ℕ) : ℝ) ^ 2),
          Finset.prod_pow, ← Nat.cast_prod]
    rw [hprod]
    have hcast : ((∏ p ∈ highPrimeSet q, (q.factorization p + 1) : ℕ) : ℝ)
        ≤ (q.divisors.card : ℝ) := Nat.cast_le.mpr hmain
    exact pow_le_pow_left₀ (by positivity) hcast 2
  · rw [hlog]
    exact Real.rpow_le_rpow (by positivity) (Nat.cast_le.mpr hHle) (by norm_num)
  · have h3d : 3 ^ d.primeFactors.card ≤ q.divisors.card :=
      le_trans (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 3) hd)
        (hpow_le 3 (by norm_num))
    have hD1 : (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
      have h1 : 1 ≤ q.divisors.card :=
        le_trans (one_le_pow₀ (show (1 : ℕ) ≤ 2 by norm_num)) h2H
      exact_mod_cast h1
    calc (3 : ℝ) ^ d.primeFactors.card ≤ (q.divisors.card : ℝ) := by exact_mod_cast h3d
      _ ≤ (q.divisors.card : ℝ) ^ 2 := le_self_pow₀ hD1 (by norm_num : (2 : ℕ) ≠ 0)

end Work.LinnikBurgess
