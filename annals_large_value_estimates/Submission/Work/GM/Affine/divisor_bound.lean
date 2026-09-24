import Mathlib

/-!
# The sub-polynomial divisor bound `#(n.divisors) ≤ C_ε · n^ε`

For every `ε > 0` there is a constant `C = C(ε)` with
`#(n.divisors) ≤ C * n^ε` for all `n : ℕ`.

This is the standard "the divisor function grows slower than any power" bound (needed, for
instance, to count the resonance pairs `m₁ℓ ≈ ξ` in GM §9, Lemma 9.2).  The proof is elementary:

* `#(n.divisors) = ∏_{p | n} (a_p + 1)` where `a_p = n.factorization p`;
* for primes `p ≥ 2^{2/ε}` one has `a+1 ≤ p^{εa/2}`;
* for the finitely many primes `p < 2^{2/ε}` one has `a_p ≤ log₂ n`, so the contribution is at most
  `(log₂ n + 1)^{K}` with `K` depending only on `ε`;
* finally `log^K n ≤ C n^{ε/2}`.
-/

open Finset

namespace Work.GM.Affine

/-- Power-of-logarithm bound: for `K : ℕ` and `a > 0` there is `C` with
`(logb 2 x + 1)^K ≤ C * x^a` for all `x ≥ 1`. -/
lemma logb_two_add_one_pow_le {K : ℕ} {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.logb 2 x + 1) ^ K ≤ C * x ^ a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
  set d : ℝ := a / (2 * ((K : ℝ) + 1)) with hd
  have hdpos : 0 < d := div_pos ha hden
  set M : ℝ := 1 + 1 / (d * Real.log 2) with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : 0 ≤ 1 / (d * Real.log 2) := by positivity
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨M ^ (K + 1), by positivity, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hlogx : Real.log x ≤ x ^ d / d := Real.log_le_rpow_div hxpos.le hdpos
  have hbound : Real.logb 2 x + 1 ≤ M * x ^ d := by
    have h2 : Real.log x / Real.log 2 ≤ (x ^ d / d) / Real.log 2 :=
      div_le_div_of_nonneg_right hlogx hlog2.le
    have h3 : (x ^ d / d) / Real.log 2 = x ^ d * (1 / (d * Real.log 2)) := by
      field_simp
    have hxd1 : 1 ≤ x ^ d := Real.one_le_rpow hx hdpos.le
    have h4 : Real.log x / Real.log 2 ≤ x ^ d * (1 / (d * Real.log 2)) := by
      rw [← h3]; exact h2
    have hsum : Real.log x / Real.log 2 + 1 ≤ x ^ d * (1 / (d * Real.log 2)) + x ^ d :=
      add_le_add h4 hxd1
    have h5 : Real.logb 2 x + 1 = Real.log x / Real.log 2 + 1 := by
      simp only [Real.logb]
    calc Real.log x / Real.log 2 + 1
        ≤ x ^ d * (1 / (d * Real.log 2)) + x ^ d := hsum
      _ = M * x ^ d := by rw [hM]; ring
  have hexp : d * (K : ℝ) ≤ a := by
    have hKle : (K : ℝ) ≤ 2 * ((K : ℝ) + 1) := by
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    rw [hd, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [ha, hKle]
  have hbase : 0 ≤ Real.logb 2 x + 1 := by
    have h0 : 0 ≤ Real.logb 2 x :=
      (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) hxpos).mpr (by simpa using hx)
    linarith
  calc (Real.logb 2 x + 1) ^ K ≤ (M * x ^ d) ^ K :=
        pow_le_pow_left₀ hbase hbound K
    _ = M ^ K * x ^ (d * (K : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ d) K, Real.rpow_mul hxpos.le d (K : ℝ)]
    _ ≤ M ^ (K + 1) * x ^ a := by
        have h1 : M ^ K ≤ M ^ (K + 1) := by
          calc M ^ K = M ^ K * 1 := by ring
            _ ≤ M ^ K * M := mul_le_mul_of_nonneg_left hM1 (by positivity)
            _ = M ^ (K + 1) := by ring
        have h2 : x ^ (d * (K : ℝ)) ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hx hexp
        calc M ^ K * x ^ (d * (K : ℝ)) ≤ M ^ (K + 1) * x ^ (d * (K : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hxpos.le _)
          _ ≤ M ^ (K + 1) * x ^ a := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Divisor bound.** For every `ε > 0` there is `C > 0` with `#(n.divisors) ≤ C * n^ε` for all
`n : ℕ`. -/
theorem card_divisors_le_const_mul_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set ρ : ℝ := ε / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hεeq : ε = 2 * ρ := by rw [hρ]; ring
  set A : ℝ := 2 ^ (2 / ε) with hA
  have hA1 : 1 ≤ A := Real.one_le_rpow (by norm_num) (by positivity)
  have hArho : A ^ ρ = 2 := by
    rw [hA, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : 2 / ε * ρ = 1 := by rw [hρ]; field_simp
    rw [hexp, Real.rpow_one]
  set K : ℕ := ⌈A⌉₊ + 1 with hK
  obtain ⟨C₁, hC₁pos, hC₁⟩ := logb_two_add_one_pow_le (K := K) (a := ρ) hρpos
  refine ⟨max 1 C₁, lt_of_lt_of_le one_pos (le_max_left _ _), fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show (Nat.divisors 0).card = 0 from by simp, Nat.cast_zero, Real.zero_rpow (ne_of_gt hε)]
    positivity
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.divisors_one, Finset.card_singleton, Nat.cast_one, Real.one_rpow, mul_one]
    exact le_max_left 1 C₁
  have hn2 : 2 ≤ n := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- the two classes of primes
  have hsmall_count : (n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ)))).card ≤ K := by
    have hsub : n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))) ⊆ Finset.range K := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      have hpa : (p : ℝ) < A := not_le.mp hp.2
      have hceil : A ≤ ((⌈A⌉₊ : ℕ) : ℝ) := Nat.le_ceil A
      have : p ≤ ⌈A⌉₊ := by exact_mod_cast le_of_lt (lt_of_lt_of_le hpa hceil)
      rw [hK]; omega
    calc (n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ)))).card
        ≤ (Finset.range K).card := Finset.card_le_card hsub
      _ = K := Finset.card_range K
  -- the exponent of a prime divisor is at most `log₂ n`
  have hfac_le : ∀ p ∈ n.primeFactors, (n.factorization p : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpprime.two_le
    have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hle : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) hdvd
    have h2 : (2 : ℕ) ^ n.factorization p ≤ n :=
      le_trans (Nat.pow_le_pow_left hp2 _) hle
    have h2' : (2 : ℝ) ^ ((n.factorization p : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast h2
    exact (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) hnpos).mpr h2'
  -- large primes: `a + 1 ≤ p^(ρ a)`
  have hlarge : ∀ p ∈ n.primeFactors, A ≤ (p : ℝ) →
      ((n.factorization p + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (ρ * (n.factorization p : ℝ)) := by
    intro p hp hAp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpprime.two_le
    have hppos : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hprho : 2 ≤ (p : ℝ) ^ ρ := by
      have hmono : A ^ ρ ≤ (p : ℝ) ^ ρ := Real.rpow_le_rpow (by positivity) hAp hρpos.le
      rwa [hArho] at hmono
    rcases eq_or_lt_of_le (Nat.zero_le (n.factorization p)) with h0 | hpos
    · rw [← h0]; norm_num
    · have hnat : n.factorization p + 1 ≤ 2 ^ n.factorization p := by
        induction n.factorization p with
        | zero => omega
        | succ k ih => rw [pow_succ]; omega
      have h1 : ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n.factorization p) := by
        have : ((2 : ℕ) ^ n.factorization p : ℕ) ≤ (2 : ℝ) ^ (n.factorization p) := by
          push_cast; exact le_rfl
        calc ((n.factorization p + 1 : ℕ) : ℝ) ≤ ((2 : ℕ) ^ n.factorization p : ℝ) := by
              exact_mod_cast hnat
          _ = (2 : ℝ) ^ (n.factorization p) := by push_cast; ring
      have h2 : (2 : ℝ) ^ (n.factorization p) ≤ ((p : ℝ) ^ ρ) ^ (n.factorization p) :=
        pow_le_pow_left₀ (by norm_num) hprho _
      calc ((n.factorization p + 1 : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (n.factorization p) := h1
        _ ≤ ((p : ℝ) ^ ρ) ^ (n.factorization p) := h2
        _ = (p : ℝ) ^ (ρ * (n.factorization p : ℝ)) := by
            rw [← Real.rpow_natCast ((p : ℝ) ^ ρ) (n.factorization p), ← Real.rpow_mul hppos]
  -- factorisation of the divisor count
  have hcard : (n.divisors.card : ℝ)
      = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hn, Nat.cast_prod]
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := n.primeFactors)
    (p := fun p : ℕ => A ≤ (p : ℝ)) (f := fun p : ℕ => ((n.factorization p + 1 : ℕ) : ℝ))
  -- the large primes contribute at most `n^ρ`
  have hbig : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
        ((n.factorization p + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ ρ := by
    have step1 : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
          ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            (p : ℝ) ^ (ρ * (n.factorization p : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp; positivity
      · intro p hp
        exact hlarge p (Finset.mem_of_mem_filter p hp) (Finset.mem_filter.mp hp).2
    have step2 : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            (p : ℝ) ^ (ρ * (n.factorization p : ℝ)))
        = (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            (p : ℝ) ^ (n.factorization p : ℝ)) ^ ρ := by
      rw [Finset.prod_congr rfl (fun p _ => by
            rw [mul_comm, Real.rpow_mul (by positivity : (0:ℝ) ≤ (p:ℝ))]), Real.finsetProd_rpow]
      intro p hp; positivity
    have step3 : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            (p : ℝ) ^ (n.factorization p : ℝ)) ≤ (n : ℝ) := by
      calc (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
              (p : ℝ) ^ (n.factorization p : ℝ))
          ≤ ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℝ) := by
            apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
            · intro p hp; positivity
            · intro p hp _
              exact Real.one_le_rpow (by
                have := Nat.prime_of_mem_primeFactors hp
                exact_mod_cast this.one_lt.le) (by positivity)
        _ = (n : ℝ) := by
            have hcast : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℝ))
                = ∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ) := by
              apply Finset.prod_congr rfl
              intro p _
              rw [Real.rpow_natCast, Nat.cast_pow]
            rw [hcast, ← Nat.cast_prod, ← Nat.prod_primeFactors_pow_factorization hn]
    calc (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            (p : ℝ) ^ (n.factorization p : ℝ)) ^ ρ := by
          rw [← step2]; exact step1
      _ ≤ (n : ℝ) ^ ρ := Real.rpow_le_rpow (by positivity) step3 hρpos.le
  -- the small primes contribute at most `(log₂ n + 1)^K`
  have hsmall : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))),
        ((n.factorization p + 1 : ℕ) : ℝ)) ≤ (Real.logb 2 (n : ℝ) + 1) ^ K := by
    have step1 : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))),
          ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))),
            (Real.logb 2 (n : ℝ) + 1) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have := hfac_le p (Finset.mem_of_mem_filter p hp)
        positivity
      · intro p hp
        have h1 := hfac_le p (Finset.mem_of_mem_filter p hp)
        push_cast
        linarith
    have hbase_nn : (1 : ℝ) ≤ Real.logb 2 (n : ℝ) + 1 := by
      have h0 : 0 ≤ Real.logb 2 (n : ℝ) :=
        (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) hnpos).mpr (by simpa using hn1')
      linarith
    calc (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))),
            ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))),
            (Real.logb 2 (n : ℝ) + 1) := step1
      _ = (Real.logb 2 (n : ℝ) + 1) ^ (n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ)))).card :=
          Finset.prod_const _
      _ ≤ (Real.logb 2 (n : ℝ) + 1) ^ K :=
          pow_le_pow_right₀ hbase_nn hsmall_count
  -- assembly
  have hmain : (n.divisors.card : ℝ) ≤ (Real.logb 2 (n : ℝ) + 1) ^ K * (n : ℝ) ^ ρ := by
    rw [hcard, ← hsplit]
    calc (∏ p ∈ n.primeFactors.filter (fun p : ℕ => A ≤ (p : ℝ)),
            ((n.factorization p + 1 : ℕ) : ℝ))
          * ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (A ≤ (p : ℝ))),
              ((n.factorization p + 1 : ℕ) : ℝ)
        ≤ (n : ℝ) ^ ρ * (Real.logb 2 (n : ℝ) + 1) ^ K :=
          mul_le_mul hbig hsmall (by positivity) (by positivity)
      _ = (Real.logb 2 (n : ℝ) + 1) ^ K * (n : ℝ) ^ ρ := by ring
  calc (n.divisors.card : ℝ)
      ≤ (Real.logb 2 (n : ℝ) + 1) ^ K * (n : ℝ) ^ ρ := hmain
    _ ≤ (C₁ * (n : ℝ) ^ ρ) * (n : ℝ) ^ ρ :=
        mul_le_mul_of_nonneg_right (hC₁ (n : ℝ) hn1') (Real.rpow_nonneg hnpos.le ρ)
    _ = C₁ * (n : ℝ) ^ ε := by
        have hsum : ρ + ρ = ε := by rw [hεeq]; ring
        rw [mul_assoc, ← Real.rpow_add hnpos, hsum]
    _ ≤ max 1 C₁ * (n : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right (le_max_right 1 C₁) (Real.rpow_nonneg hnpos.le ε)

end Work.GM.Affine
