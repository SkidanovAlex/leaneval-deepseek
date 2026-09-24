import Mathlib

/-!
# A power-saving bound for the divisor function

For every `δ > 0` there is `C > 0` with `d(n) ≤ C · n^δ` for all `n ≥ 1`, where
`d(n) = n.divisors.card` is the number of divisors of `n`.

This is the ubiquitous "`d(n) ≪_δ n^δ`" estimate.  The proof is the standard
one: by unique factorisation `d(n) = ∏_{p | n} (a_p + 1)` and `n = ∏_{p | n} p^{a_p}`.
For an exponent `a` and a prime `p` with `p^δ ≥ 2` one has
`a + 1 ≤ 2^a ≤ (p^δ)^a`.  For the finitely many *small* primes `p^δ < 2` one
pays a constant factor per prime, and there are boundedly many of them
(at most `⌈2^{1/δ}⌉`).  Here the constant factor is obtained from the elementary
observation that for `m` with `(2^δ)^m ≥ 2` and `a = m·q + r`,
`a + 1 ≤ m·(q+1) ≤ m·2^q ≤ m·(2^δ)^a`.
-/

namespace Work.GM.S2

open Finset

private lemma succ_le_mul_pow (q : ℝ) (hq : 1 ≤ q) {m : ℕ} (hm : 2 ≤ q ^ m) (a : ℕ) :
    (a : ℝ) + 1 ≤ (m : ℝ) * q ^ a := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm
    · exact h
  have h1 : (a : ℝ) + 1 ≤ (m : ℝ) * (((a / m : ℕ) : ℝ) + 1) := by
    have hnat : a + 1 ≤ m * (a / m + 1) := by
      have hmod : a % m < m := Nat.mod_lt a (by omega)
      have hd : m * (a / m) + a % m = a := Nat.div_add_mod a m
      have key : m * (a / m + 1) = m * (a / m) + m := by ring
      rw [key]; omega
    exact_mod_cast hnat
  have h2 : ((a / m : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (a / m) := by
    have : a / m + 1 ≤ 2 ^ (a / m) := Nat.succ_le_of_lt Nat.lt_two_pow_self
    exact_mod_cast this
  have h3 : (2 : ℝ) ^ (a / m) ≤ (q ^ m) ^ (a / m) := pow_le_pow_left₀ (by norm_num) hm (a / m)
  have h4 : (q ^ m) ^ (a / m) ≤ q ^ a := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hq (Nat.mul_div_le a m)
  calc (a : ℝ) + 1 ≤ (m : ℝ) * (((a / m : ℕ) : ℝ) + 1) := h1
    _ ≤ (m : ℝ) * (2 : ℝ) ^ (a / m) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (m : ℝ) * (q ^ m) ^ (a / m) := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (m : ℝ) * q ^ a := by
        apply mul_le_mul_of_nonneg_left h4 (by positivity)

/-- For a prime `p` with `p^δ ≥ 2`, the factor `a + 1` of the divisor count is
absorbed by `(p^δ)^a`. -/
private lemma large_factor (p : ℕ) (δ : ℝ) (a : ℕ) (hp2 : (2 : ℝ) ≤ (p : ℝ) ^ δ) :
    (a : ℝ) + 1 ≤ ((p : ℝ) ^ δ) ^ a := by
  have h1 : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := by
    have : a + 1 ≤ 2 ^ a := Nat.succ_le_of_lt Nat.lt_two_pow_self
    exact_mod_cast this
  exact h1.trans (pow_le_pow_left₀ (by norm_num) hp2 a)

/-- For a *small* prime `p ≥ 2` (i.e. `p^δ < 2`) the factor `a + 1` is bounded by
`m · (p^δ)^a`, where `m` is any integer with `(2^δ)^m ≥ 2`. -/
private lemma small_factor (p : ℕ) (δ : ℝ) (a m : ℕ) (hδ : 0 ≤ δ) (hq : 1 ≤ (2 : ℝ) ^ δ)
    (hm2 : 2 ≤ ((2 : ℝ) ^ δ) ^ m) (hp2 : (2 : ℝ) ≤ (p : ℝ)) :
    (a : ℝ) + 1 ≤ (m : ℝ) * ((p : ℝ) ^ δ) ^ a := by
  have h1 := succ_le_mul_pow ((2 : ℝ) ^ δ) hq hm2 a
  have h2 : ((2 : ℝ) ^ δ) ^ a ≤ ((p : ℝ) ^ δ) ^ a :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hδ) a
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

set_option maxHeartbeats 1000000 in
theorem divisor_bound : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ δ := by
  intro δ hδ
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  obtain ⟨m, hm_ge⟩ := exists_nat_ge (1 / δ)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have hpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hm_ge
    have hmpos : 0 < m := by exact_mod_cast hpos
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hδm : (1 : ℝ) ≤ δ * (m : ℝ) := by
    have h' : (1 : ℝ) ≤ (m : ℝ) * δ := (div_le_iff₀ hδ).mp hm_ge
    linarith
  have hq : (1 : ℝ) ≤ (2 : ℝ) ^ δ := Real.one_le_rpow (by norm_num) hδ0
  have hm2 : (2 : ℝ) ≤ ((2 : ℝ) ^ δ) ^ m := by
    have h1 : ((2 : ℝ) ^ δ) ^ m = (2 : ℝ) ^ (δ * (m : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ δ) m, ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h1]
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hδm
    rwa [Real.rpow_one] at this
  set T : ℝ := (2 : ℝ) ^ (1 / δ) with hT
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge T
  refine ⟨(m : ℝ) ^ N₀, pow_pos (by linarith : (0 : ℝ) < (m : ℝ)) N₀, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  let s : Finset ℕ := n.primeFactors.filter (fun p => (p : ℝ) < T)
  let l : Finset ℕ := n.primeFactors.filter (fun p => ¬ (p : ℝ) < T)
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    push_cast
    ring
  have hsplit : (∏ p ∈ s, ((n.factorization p : ℝ) + 1)) * (∏ p ∈ l, ((n.factorization p : ℝ) + 1))
      = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) :=
    Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => (p : ℝ) < T) _
  have hsplit_g : (∏ p ∈ s, ((p : ℝ) ^ δ) ^ (n.factorization p))
      * (∏ p ∈ l, ((p : ℝ) ^ δ) ^ (n.factorization p))
      = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) :=
    Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => (p : ℝ) < T) _
  have hsmall : (∏ p ∈ s, ((n.factorization p : ℝ) + 1))
      ≤ (m : ℝ) ^ s.card * ∏ p ∈ s, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    calc (∏ p ∈ s, ((n.factorization p : ℝ) + 1))
        ≤ ∏ p ∈ s, (m : ℝ) * ((p : ℝ) ^ δ) ^ (n.factorization p) := by
          apply Finset.prod_le_prod₀
          · intro p hp; positivity
          · intro p hp
            have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            exact small_factor p δ _ m hδ0 hq hm2 (by exact_mod_cast hpprime.two_le)
      _ = (∏ p ∈ s, (m : ℝ)) * ∏ p ∈ s, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
          rw [Finset.prod_mul_distrib]
      _ = (m : ℝ) ^ s.card * ∏ p ∈ s, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
          rw [Finset.prod_const]
  have hlarge : (∏ p ∈ l, ((n.factorization p : ℝ) + 1))
      ≤ ∏ p ∈ l, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hpT : T ≤ (p : ℝ) := not_lt.mp hmem.2
      have hp2 : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
        have hTδ : T ^ δ = 2 := by
          rw [hT, ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num), one_div_mul_cancel hδ.ne']
          rw [Real.rpow_one]
        rw [← hTδ]
        exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hpT hδ0
      exact large_factor p δ _ hp2
  have hC : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p)) = (n : ℝ) := by
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_pow]
  have stepA : ∀ p ∈ n.primeFactors,
      ((p : ℝ) ^ δ) ^ (n.factorization p) = ((p : ℝ) ^ (n.factorization p)) ^ δ := by
    intro p hp
    rw [← Real.rpow_natCast ((p : ℝ) ^ δ) (n.factorization p),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    rw [mul_comm δ ((n.factorization p : ℕ) : ℝ)]
    rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    rw [Real.rpow_natCast]
  have hprod_eq : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) = (n : ℝ) ^ δ := by
    rw [Finset.prod_congr rfl stepA, ← hC,
      ← Real.finsetProd_rpow n.primeFactors (fun p => (p : ℝ) ^ (n.factorization p))
        (fun p hp => by positivity) δ]
  have hscard : s.card ≤ N₀ := by
    calc s.card ≤ (Finset.range N₀).card := by
          apply Finset.card_le_card
          intro p hp
          have hpT : (p : ℝ) < T := (Finset.mem_filter.mp hp).2
          rw [Finset.mem_range]
          exact_mod_cast (lt_of_lt_of_le hpT hN₀)
      _ = N₀ := Finset.card_range N₀
  have h1 : (n.divisors.card : ℝ)
      ≤ (m : ℝ) ^ s.card * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    rw [hcard, ← hsplit]
    calc (∏ p ∈ s, ((n.factorization p : ℝ) + 1)) * (∏ p ∈ l, ((n.factorization p : ℝ) + 1))
        ≤ ((m : ℝ) ^ s.card * ∏ p ∈ s, ((p : ℝ) ^ δ) ^ (n.factorization p))
            * (∏ p ∈ l, ((p : ℝ) ^ δ) ^ (n.factorization p)) :=
          mul_le_mul hsmall hlarge (by positivity) (by positivity)
      _ = (m : ℝ) ^ s.card * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := by
          rw [mul_assoc, hsplit_g]
  calc (n.divisors.card : ℝ)
      ≤ (m : ℝ) ^ s.card * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ (n.factorization p) := h1
    _ = (m : ℝ) ^ s.card * (n : ℝ) ^ δ := by rw [hprod_eq]
    _ ≤ (m : ℝ) ^ N₀ * (n : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hm1 hscard)
          (Real.rpow_nonneg (by positivity) δ)

end Work.GM.S2
