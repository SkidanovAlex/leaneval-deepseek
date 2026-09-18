import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.DuffinSchaeffer

open Finset

/-- The exponent of a prime `q` in the product of the primes of a finset `s`
is `1` if `q ∈ s` and `0` otherwise. -/
lemma factorization_prod_of_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (q : ℕ) :
    (∏ p ∈ s, p).factorization q = if q ∈ s then 1 else 0 := by
  rw [Nat.factorization_prod_apply (fun x hx => (hs x hx).ne_zero)]
  trans ∑ x ∈ s, (if x = q then 1 else 0)
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.Prime.factorization (hs x hx), Finsupp.single_apply]
  · rw [Finset.sum_ite_eq' s q (fun _ => 1)]

/-- Two natural numbers whose exponents at every prime differ by at most one satisfy
`b + [a = b+1] = [b = a+1] + a`. -/
lemma hit_arith {a b : ℕ} (hab : a ≤ b + 1) (hba : b ≤ a + 1) :
    b + (if a = b + 1 then 1 else 0) = (if b = a + 1 then 1 else 0) + a := by
  by_cases h1 : a = b + 1
  · have h2 : ¬ (b = a + 1) := by omega
    rw [if_pos h1, if_neg h2]; omega
  · by_cases h2 : b = a + 1
    · rw [if_neg h1, if_pos h2]; omega
    · rw [if_neg h1, if_neg h2]; omega

/-- The `q`-adic valuation of the product of the primes `p` dividing `N` with
`padicValNat p N = padicValNat p v + 1` is the indicator of `N.factorization q = v.factorization q + 1`. -/
lemma factorization_filter_prod_left (N v q : ℕ) :
    (∏ p ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1), p).factorization q
      = if N.factorization q = v.factorization q + 1 then 1 else 0 := by
  have hs : ∀ p ∈ (Nat.primeFactors N).filter
      (fun p => padicValNat p N = padicValNat p v + 1), p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
  rw [factorization_prod_of_primes hs q]
  have hiff : q ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1)
      ↔ N.factorization q = v.factorization q + 1 := by
    constructor
    · intro hq
      obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hq
      have hpq := Nat.prime_of_mem_primeFactors hmem
      rw [Nat.factorization_def N hpq, Nat.factorization_def v hpq]
      exact hcond
    · intro h
      have hne : N.factorization q ≠ 0 := by omega
      have hmem : q ∈ Nat.primeFactors N := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hne
      have hpq := Nat.prime_of_mem_primeFactors hmem
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      rw [Nat.factorization_def N hpq, Nat.factorization_def v hpq] at h
      exact h
  by_cases h : q ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]

/-- Symmetric variant of `factorization_filter_prod_left`. -/
lemma factorization_filter_prod_right (N v q : ℕ) :
    (∏ p ∈ (Nat.primeFactors v).filter (fun p => padicValNat p v = padicValNat p N + 1), p).factorization q
      = if v.factorization q = N.factorization q + 1 then 1 else 0 := by
  have hs : ∀ p ∈ (Nat.primeFactors v).filter
      (fun p => padicValNat p v = padicValNat p N + 1), p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
  rw [factorization_prod_of_primes hs q]
  have hiff : q ∈ (Nat.primeFactors v).filter (fun p => padicValNat p v = padicValNat p N + 1)
      ↔ v.factorization q = N.factorization q + 1 := by
    constructor
    · intro hq
      obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hq
      have hpq := Nat.prime_of_mem_primeFactors hmem
      rw [Nat.factorization_def v hpq, Nat.factorization_def N hpq]
      exact hcond
    · intro h
      have hne : v.factorization q ≠ 0 := by omega
      have hmem : q ∈ Nat.primeFactors v := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hne
      have hpq := Nat.prime_of_mem_primeFactors hmem
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      rw [Nat.factorization_def v hpq, Nat.factorization_def N hpq] at h
      exact h
  by_cases h : q ∈ (Nat.primeFactors v).filter (fun p => padicValNat p v = padicValNat p N + 1)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]

theorem padic_ratio_decomp (N v : ℕ) (hN : 0 < N) (hv : 0 < v)
    (hupper : ∀ p : ℕ, p.Prime → padicValNat p v ≤ padicValNat p N + 1)
    (hlower : ∀ p : ℕ, p.Prime → padicValNat p N ≤ padicValNat p v + 1) :
    v * (∏ p ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1), p)
      = (∏ p ∈ (Nat.primeFactors v).filter (fun p => padicValNat p v = padicValNat p N + 1), p) * N := by
  set A := ∏ p ∈ (Nat.primeFactors N).filter (fun p => padicValNat p N = padicValNat p v + 1), p with hA
  set B := ∏ p ∈ (Nat.primeFactors v).filter (fun p => padicValNat p v = padicValNat p N + 1), p with hB
  have hbound : ∀ q, N.factorization q ≤ v.factorization q + 1 ∧
      v.factorization q ≤ N.factorization q + 1 := by
    intro q
    by_cases hq : q.Prime
    · rw [Nat.factorization_def N hq, Nat.factorization_def v hq]
      exact ⟨hlower q hq, hupper q hq⟩
    · rw [Nat.factorization_eq_zero_of_not_prime N hq, Nat.factorization_eq_zero_of_not_prime v hq]
      simp
  have hAne : A ≠ 0 := by
    rw [hA]
    exact (Finset.prod_pos (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)).ne'
  have hBne : B ≠ 0 := by
    rw [hB]
    exact (Finset.prod_pos (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)).ne'
  have hAq : ∀ q, A.factorization q = if N.factorization q = v.factorization q + 1 then 1 else 0 := by
    intro q
    rw [hA]
    exact factorization_filter_prod_left N v q
  have hBq : ∀ q, B.factorization q = if v.factorization q = N.factorization q + 1 then 1 else 0 := by
    intro q
    rw [hB]
    exact factorization_filter_prod_right N v q
  apply Nat.eq_of_factorization_eq (mul_ne_zero hv.ne' hAne) (mul_ne_zero hBne hN.ne')
  intro q
  rw [Nat.factorization_mul hv.ne' hAne, Nat.factorization_mul hBne hN.ne',
    Finsupp.add_apply, Finsupp.add_apply, hAq q, hBq q]
  exact hit_arith (hbound q).1 (hbound q).2

end Commons.NumberTheory.DuffinSchaeffer