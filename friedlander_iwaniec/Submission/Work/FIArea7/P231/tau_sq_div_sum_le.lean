import Mathlib

set_option autoImplicit false

open Finset

namespace Work.FIArea7.P231

/-- `2a+1 ≤ 3^a` for all `a`. -/
lemma p231_two_mul_add_one_le_three_pow (a : ℕ) : (2 * (a:ℝ) + 1) ≤ (3:ℝ)^a := by
  induction a with
  | zero => norm_num
  | succ k ih =>
    have hk : (1:ℝ) ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num)
    have hcast : (2 * ((k+1:ℕ):ℝ) + 1) = (2*(k:ℝ)+1) + 2 := by push_cast; ring
    rw [hcast, pow_succ]
    nlinarith [ih, hk]

/-- `(2a+1)^2 ≤ 9·2^a`. -/
lemma p231_two_mul_add_one_sq_le (a : ℕ) : (2*a+1)^2 ≤ 9 * 2^a := by
  induction a with
  | zero => norm_num
  | succ k ih =>
    have hsub : 8*k + 8 ≤ 9 * 2^k := by
      have h : k + 1 ≤ 2^k := Nat.lt_two_pow_self (n:=k)
      nlinarith
    calc (2*(k+1)+1)^2 = (2*k+1)^2 + (8*k+8) := by ring
      _ ≤ 9*2^k + 9*2^k := add_le_add ih hsub
      _ = 9 * 2^(k+1) := by rw [pow_succ]; ring

/-- `2a+1 ≤ 3·2^{a/2}`. -/
lemma p231_two_mul_add_one_le_three_mul_rpow (a : ℕ) :
    (2*(a:ℝ)+1) ≤ 3 * (2:ℝ)^((a:ℝ)/2) := by
  have hsq : (2*(a:ℝ)+1)^2 ≤ 9 * (2:ℝ)^a := by
    have h := p231_two_mul_add_one_sq_le a
    have hc : (((2*a+1)^2 : ℕ) : ℝ) ≤ ((9*2^a : ℕ) : ℝ) := by exact_mod_cast h
    simpa using hc
  have hpow : (2:ℝ)^a = ((2:ℝ)^((a:ℝ)/2))^2 := by
    rw [← Real.rpow_natCast (2:ℝ) a, sq, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [hpow] at hsq
  have hrhs : 9 * ((2:ℝ)^((a:ℝ)/2))^2 = (3 * (2:ℝ)^((a:ℝ)/2))^2 := by ring
  rw [hrhs] at hsq
  have hx : (0:ℝ) ≤ 2*(a:ℝ)+1 := by positivity
  have hy : (0:ℝ) ≤ 3 * (2:ℝ)^((a:ℝ)/2) := by positivity
  nlinarith [hsq, hx, hy]

/-- Small-prime factor bound: for a prime `p ≤ 9` and any `a`, `2a+1 ≤ 3·p^{a/2}`. -/
lemma p231_small_prime_bound (p a : ℕ) (hp : p.Prime) (hp9 : p ≤ 9) :
    (2*(a:ℝ)+1) ≤ 3 * (p:ℝ)^((a:ℝ)/2) := by
  have h := p231_two_mul_add_one_le_three_mul_rpow a
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hle : (2:ℝ)^((a:ℝ)/2) ≤ (p:ℝ)^((a:ℝ)/2) :=
    Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
  calc (2*(a:ℝ)+1) ≤ 3 * (2:ℝ)^((a:ℝ)/2) := h
    _ ≤ 3 * (p:ℝ)^((a:ℝ)/2) := by apply mul_le_mul_of_nonneg_left hle; norm_num

/-- Large-prime factor bound: for a prime `p ≥ 9` and any `a`, `2a+1 ≤ p^{a/2}`. -/
lemma p231_large_prime_bound (p a : ℕ) (hp : p.Prime) (hp9 : 9 ≤ p) :
    (2*(a:ℝ)+1) ≤ (p:ℝ)^((a:ℝ)/2) := by
  have h := p231_two_mul_add_one_le_three_pow a
  have hsqrt : (3:ℝ) ≤ (p:ℝ)^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
    exact_mod_cast hp9
  have hpow : (3:ℝ)^a ≤ ((p:ℝ)^((1:ℝ)/2))^a := pow_le_pow_left₀ (by norm_num) hsqrt a
  have hrewrite : ((p:ℝ)^((1:ℝ)/2))^a = (p:ℝ)^((a:ℝ)/2) := by
    rw [← Real.rpow_natCast ((p:ℝ)^((1:ℝ)/2)) a,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p:ℝ))]
    congr 1; ring
  rw [hrewrite] at hpow
  linarith

/-- Divisor count of `g^2` rewritten via the prime factorization of `g`. -/
lemma p231_card_divisors_sq_eq (g : ℕ) (hg : 1 ≤ g) :
    (((g^2).divisors.card : ℕ) : ℝ)
      = ∏ p ∈ g.primeFactors, ((2 * g.factorization p + 1 : ℕ) : ℝ) := by
  have hg0 : g ≠ 0 := by omega
  have hpf : (g^2).primeFactors = g.primeFactors := Nat.primeFactors_pow g (by norm_num)
  have hfac : ∀ x, (g^2).factorization x = 2 * g.factorization x := by
    intro x
    rw [Nat.factorization_pow]
    simp [Finsupp.smul_apply]
  rw [Nat.card_divisors (pow_ne_zero 2 hg0), hpf, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [hfac p]

/-- `∏_{p | g} p^{v_p(g)/2} = g^{1/2}`. -/
lemma p231_prod_rpow_eq_sqrt (g : ℕ) (hg : 1 ≤ g) :
    ∏ p ∈ g.primeFactors, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)
      = (g:ℝ)^(1/2:ℝ) := by
  have hg0 : g ≠ 0 := by omega
  have hg_eq : (g:ℝ) = ∏ p ∈ g.primeFactors, (p:ℝ)^(g.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hg0]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    push_cast
    ring
  have hterm : ∀ p : ℕ, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)
      = ((p:ℝ)^(g.factorization p))^(1/2:ℝ) := by
    intro p
    rw [← Real.rpow_natCast (p:ℝ) (g.factorization p),
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p:ℝ))]
    congr 1
    ring
  simp_rw [hterm]
  rw [Real.finsetProd_rpow _ _ _ (1/2:ℝ)]
  · rw [← hg_eq]
  · intro p hp; positivity

/-- Pointwise bound `τ(g²) ≤ 81·√g`. -/
lemma p231_sq_divisors_card_le (g : ℕ) (hg : 1 ≤ g) :
    (((g^2).divisors.card : ℕ) : ℝ) ≤ 81 * (g:ℝ)^(1/2:ℝ) := by
  have hcard := p231_card_divisors_sq_eq g hg
  have hsqrt := p231_prod_rpow_eq_sqrt g hg
  -- card of the set of small primes
  have hcard_small : (g.primeFactors.filter (fun p => p ≤ 9)).card ≤ 4 := by
    have hsub : g.primeFactors.filter (fun p => p ≤ 9) ⊆ ({2,3,5,7} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hps, hp9⟩ := hp
      have hprime : p.Prime := (Nat.mem_primeFactors.mp hps).1
      have hp2 : 2 ≤ p := hprime.two_le
      interval_cases p <;> simp only [Finset.mem_insert, Finset.mem_singleton]
      · trivial
      · trivial
      · exact absurd hprime (by norm_num)
      · trivial
      · exact absurd hprime (by norm_num)
      · trivial
      · exact absurd hprime (by norm_num)
      · exact absurd hprime (by norm_num)
    calc (g.primeFactors.filter (fun p => p ≤ 9)).card
        ≤ ({2,3,5,7} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 4 := by decide
  -- the two filtered products
  have hsmall_le : (∏ p ∈ g.primeFactors with p ≤ 9, ((2 * g.factorization p + 1 : ℕ) : ℝ))
      ≤ (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
          * (∏ p ∈ g.primeFactors with p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := by
    calc (∏ p ∈ g.primeFactors with p ≤ 9, ((2 * g.factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ g.primeFactors with p ≤ 9,
            (3 * (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := by
          apply Finset.prod_le_prod₀
          · intro p hp; positivity
          · intro p hp
            rw [Finset.mem_filter] at hp
            have hprime : p.Prime := (Nat.mem_primeFactors.mp hp.1).1
            push_cast
            exact p231_small_prime_bound p (g.factorization p) hprime hp.2
      _ = (∏ p ∈ g.primeFactors with p ≤ 9, (3:ℝ))
            * (∏ p ∈ g.primeFactors with p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := by
          rw [Finset.prod_mul_distrib]
      _ = (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
            * (∏ p ∈ g.primeFactors with p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := by
          rw [Finset.prod_const]
  have hlarge_le :
      (∏ p ∈ g.primeFactors with ¬ p ≤ 9, ((2 * g.factorization p + 1 : ℕ) : ℝ))
      ≤ ∏ p ∈ g.primeFactors with ¬ p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2) := by
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      rw [Finset.mem_filter] at hp
      have hprime : p.Prime := (Nat.mem_primeFactors.mp hp.1).1
      have hp9 : 9 ≤ p := by omega
      push_cast
      exact p231_large_prime_bound p (g.factorization p) hprime hp9
  -- combine
  have hsplit := Finset.prod_filter_mul_prod_filter_not g.primeFactors (fun p => p ≤ 9)
      (fun p => ((2 * g.factorization p + 1 : ℕ) : ℝ))
  have hsplitQ := Finset.prod_filter_mul_prod_filter_not g.primeFactors (fun p => p ≤ 9)
      (fun p => (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2))
  have hprod_le :
      (∏ p ∈ g.primeFactors, ((2 * g.factorization p + 1 : ℕ) : ℝ))
      ≤ (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
          * (∏ p ∈ g.primeFactors, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := by
    rw [← hsplit]
    calc (∏ p ∈ g.primeFactors with p ≤ 9, ((2 * g.factorization p + 1 : ℕ) : ℝ))
          * (∏ p ∈ g.primeFactors with ¬ p ≤ 9, ((2 * g.factorization p + 1 : ℕ) : ℝ))
        ≤ ((3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
              * (∏ p ∈ g.primeFactors with p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)))
            * (∏ p ∈ g.primeFactors with ¬ p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) :=
          mul_le_mul hsmall_le hlarge_le (by positivity) (by positivity)
      _ = (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
            * ((∏ p ∈ g.primeFactors with p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2))
              * (∏ p ∈ g.primeFactors with ¬ p ≤ 9, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2))) := by
          ring
      _ = (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
            * (∏ p ∈ g.primeFactors, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := by
          rw [← hsplitQ]
  have h3 : (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card) ≤ 81 := by
    calc (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card) ≤ (3:ℝ)^4 :=
          pow_le_pow_right₀ (by norm_num) hcard_small
      _ = 81 := by norm_num
  calc (((g^2).divisors.card : ℕ) : ℝ)
      = ∏ p ∈ g.primeFactors, ((2 * g.factorization p + 1 : ℕ) : ℝ) := hcard
    _ ≤ (3:ℝ)^((g.primeFactors.filter (fun p => p ≤ 9)).card)
          * (∏ p ∈ g.primeFactors, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) := hprod_le
    _ ≤ 81 * (∏ p ∈ g.primeFactors, (p:ℝ)^(((g.factorization p : ℕ):ℝ)/2)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 81 * (g:ℝ)^(1/2:ℝ) := by rw [hsqrt]

/-- Summability of `g ↦ g^{-17/12}`. -/
lemma p231_summable_rpow : Summable (fun n : ℕ => (n:ℝ)^(-(17/12:ℝ))) := by
  rw [Real.summable_nat_rpow]
  norm_num

/-- The partial sums of `g ↦ g^{-17/12}` are uniformly bounded. -/
lemma p231_sum_rpow_partial_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ G : ℕ,
      (∑ g ∈ Finset.Icc 1 G, (g : ℝ) ^ (-(17 / 12 : ℝ))) ≤ K := by
  set K : ℝ := ∑' n : ℕ, (n:ℝ)^(-(17/12:ℝ)) with hK
  have hKpos : 0 < K := by
    have h1 : (1:ℝ) ≤ K := by
      have hle := p231_summable_rpow.le_tsum 1 (fun j _ => Real.rpow_nonneg (by positivity) _)
      simpa [hK] using hle
    linarith
  refine ⟨K, hKpos, fun G => ?_⟩
  exact p231_summable_rpow.sum_le_tsum (Finset.Icc 1 G)
    (fun i _ => Real.rpow_nonneg (by positivity) _)

theorem tau_sq_div_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ G : ℕ,
      (∑ g ∈ Finset.Icc 1 G, (((g ^ 2).divisors.card : ℕ) : ℝ) * (g : ℝ) ^ (-(23 / 12 : ℝ)))
        ≤ K := by
  obtain ⟨K, hKpos, hK⟩ := p231_sum_rpow_partial_bound
  refine ⟨81 * K, by positivity, fun G => ?_⟩
  calc (∑ g ∈ Finset.Icc 1 G,
          (((g ^ 2).divisors.card : ℕ) : ℝ) * (g : ℝ) ^ (-(23 / 12 : ℝ)))
      ≤ ∑ g ∈ Finset.Icc 1 G, 81 * (g:ℝ)^(-(17/12:ℝ)) := by
        apply Finset.sum_le_sum
        intro g hg
        rw [Finset.mem_Icc] at hg
        obtain ⟨hg1, _⟩ := hg
        have hgpos : (0:ℝ) < (g:ℝ) := by exact_mod_cast (by omega : 0 < g)
        have h := p231_sq_divisors_card_le g hg1
        have hpow : (g:ℝ)^(1/2:ℝ) * (g:ℝ)^(-(23/12:ℝ)) = (g:ℝ)^(-(17/12:ℝ)) := by
          rw [← Real.rpow_add hgpos]
          congr 1; norm_num
        calc (((g^2).divisors.card : ℕ):ℝ) * (g:ℝ)^(-(23/12:ℝ))
            ≤ (81 * (g:ℝ)^(1/2:ℝ)) * (g:ℝ)^(-(23/12:ℝ)) :=
              mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by positivity) _)
          _ = 81 * ((g:ℝ)^(1/2:ℝ) * (g:ℝ)^(-(23/12:ℝ))) := by ring
          _ = 81 * (g:ℝ)^(-(17/12:ℝ)) := by rw [hpow]
    _ = 81 * (∑ g ∈ Finset.Icc 1 G, (g:ℝ)^(-(17/12:ℝ))) := by rw [Finset.mul_sum]
    _ ≤ 81 * K := mul_le_mul_of_nonneg_left (hK G) (by norm_num)

end Work.FIArea7.P231
