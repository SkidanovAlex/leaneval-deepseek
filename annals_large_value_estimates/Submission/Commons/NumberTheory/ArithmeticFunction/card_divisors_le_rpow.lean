import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Commons.NumberTheory.ArithmeticFunction

/-- For every real `q > 1` there is a constant `K ≥ 1` with `n + 1 ≤ K * q ^ n` for all `n`. -/
lemma succ_le_mul_pow (q : ℝ) (hq : 1 < q) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (n : ℝ) + 1 ≤ K * q ^ n := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 : ℝ) hq
  have hmpos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; norm_num at hm
    · exact h
  refine ⟨(m : ℝ), by exact_mod_cast hmpos, ?_⟩
  intro n
  rcases lt_or_ge n m with hnm | hmn
  · have h1 : (n : ℝ) + 1 ≤ (m : ℝ) := by
      have : n + 1 ≤ m := by omega
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq.le
    calc (n : ℝ) + 1 ≤ (m : ℝ) := h1
      _ = (m : ℝ) * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) * q ^ n := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m)
  · have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one (le_of_lt hq)
    have hq1 : (1 : ℝ) ≤ q := le_of_lt hq
    have hqm2 : (2 : ℝ) ≤ q ^ m := le_of_lt hm
    have h3 : ((n / m : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (n / m) := by
      have : n / m + 1 ≤ 2 ^ (n / m) := Nat.succ_le_iff.mpr Nat.lt_two_pow_self
      exact_mod_cast this
    have hstep : (n : ℝ) + 1 ≤ (m : ℝ) * (2 : ℝ) ^ (n / m) := by
      have h1 : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
      have h2 : ((n % m : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
        have : n % m + 1 ≤ m := by have := Nat.mod_lt n (by omega : 0 < m); omega
        exact_mod_cast this
      have hmm : (n : ℝ) + 1 ≤ (m : ℝ) * (((n / m : ℕ) : ℝ) + 1) := by
        rw [h1]; nlinarith [h2]
      exact hmm.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg m))
    have hqstep : (2 : ℝ) ^ (n / m) ≤ q ^ n := by
      have hpow : (2 : ℝ) ^ (n / m) ≤ (q ^ m) ^ (n / m) :=
        pow_le_pow_left₀ (by norm_num) hqm2 (n / m)
      have hmul : (q ^ m) ^ (n / m) = q ^ (m * (n / m)) := (pow_mul q m (n / m)).symm
      have hle2 : q ^ (m * (n / m)) ≤ q ^ (m * (n / m) + n % m) := by
        rw [pow_add]
        exact le_mul_of_one_le_right (pow_nonneg hq0 _) (one_le_pow₀ hq1)
      have hid : m * (n / m) + n % m = n := Nat.div_add_mod n m
      calc (2 : ℝ) ^ (n / m) ≤ (q ^ m) ^ (n / m) := hpow
        _ = q ^ (m * (n / m)) := hmul
        _ ≤ q ^ (m * (n / m) + n % m) := hle2
        _ = q ^ n := by rw [hid]
    calc (n : ℝ) + 1 ≤ (m : ℝ) * (2 : ℝ) ^ (n / m) := hstep
      _ ≤ (m : ℝ) * q ^ n := mul_le_mul_of_nonneg_left hqstep (Nat.cast_nonneg m)

/-- The `rpow`-product over the prime factors of `n`: `∏ p, p ^ (r * v_p(n)) = n ^ r`. -/
lemma prod_primeFactors_rpow (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    ∏ p ∈ n.primeFactors, (p : ℝ) ^ (r * (n.factorization p : ℝ)) = (n : ℝ) ^ r := by
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rfl
  calc ∏ p ∈ n.primeFactors, (p : ℝ) ^ (r * (n.factorization p : ℝ))
      = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ r := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [mul_comm r (n.factorization p : ℝ), Real.rpow_mul (by positivity),
          Real.rpow_natCast]
    _ = (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p)) ^ r := by
        rw [Real.finsetProd_rpow]
        intro p hp; positivity
    _ = (n : ℝ) ^ r := by rw [hcast]

theorem card_divisors_le_rpow (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ eps := by
  classical
  obtain ⟨K, hK1, hK⟩ := succ_le_mul_pow ((2 : ℝ) ^ eps) (Real.one_lt_rpow (by norm_num) heps)
  have hKpos : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  set B : ℕ := Nat.ceil ((2 : ℝ) ^ eps⁻¹) + 1 with hB
  refine ⟨K ^ B, by positivity, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  push_cast
  have key : (∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ))
      ≤ K ^ B * (n : ℝ) ^ eps := by
    rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors
          (fun p : ℕ => (p : ℝ) ^ eps < 2) (fun p : ℕ => ((n.factorization p + 1 : ℕ) : ℝ))]
    have per1 : ∀ (p : ℕ), p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2) →
        ((n.factorization p + 1 : ℕ) : ℝ) ≤ K * (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpP⟩ := hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hpS).two_le
      have hfac : ((n.factorization p : ℕ) : ℝ) + 1
          ≤ K * ((2 : ℝ) ^ eps) ^ n.factorization p := hK (n.factorization p)
      have hrw : ((2 : ℝ) ^ eps) ^ n.factorization p
          = (2 : ℝ) ^ (eps * (n.factorization p : ℝ)) :=
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) eps (n.factorization p)).symm
      have hmono : (2 : ℝ) ^ (eps * (n.factorization p : ℝ))
          ≤ (p : ℝ) ^ (eps * (n.factorization p : ℝ)) :=
        Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
      calc ((n.factorization p + 1 : ℕ) : ℝ)
          = ((n.factorization p : ℕ) : ℝ) + 1 := by push_cast; ring
        _ ≤ K * ((2 : ℝ) ^ eps) ^ n.factorization p := hfac
        _ = K * (2 : ℝ) ^ (eps * (n.factorization p : ℝ)) := by rw [hrw]
        _ ≤ K * (p : ℝ) ^ (eps * (n.factorization p : ℝ)) :=
            mul_le_mul_of_nonneg_left hmono hKpos
    have per2 : ∀ (p : ℕ), p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ^ eps < 2) →
        ((n.factorization p + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpP⟩ := hp
      have hpP' : (2 : ℝ) ≤ (p : ℝ) ^ eps := le_of_not_gt hpP
      have hfac : ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n.factorization p := by
        have : n.factorization p + 1 ≤ 2 ^ n.factorization p :=
          Nat.succ_le_iff.mpr Nat.lt_two_pow_self
        exact_mod_cast this
      have hbase : (2 : ℝ) ^ n.factorization p
          ≤ ((p : ℝ) ^ eps) ^ n.factorization p :=
        pow_le_pow_left₀ (by norm_num) hpP' (n.factorization p)
      have hrw : ((p : ℝ) ^ eps) ^ n.factorization p
          = (p : ℝ) ^ (eps * (n.factorization p : ℝ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg p) eps (n.factorization p)).symm
      calc ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n.factorization p := hfac
        _ ≤ ((p : ℝ) ^ eps) ^ n.factorization p := hbase
        _ = (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := hrw
    have hA : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
          ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ K ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card
            * ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
                (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
      calc (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
              ((n.factorization p + 1 : ℕ) : ℝ))
          ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
              K * (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
            apply Finset.prod_le_prod₀
            · intro p hp; positivity
            · exact per1
        _ = K ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card
              * ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
                  (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hBl : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ^ eps < 2),
          ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ^ eps < 2),
            (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp; positivity
      · exact per2
    have hcard : (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card ≤ B := by
      have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2) ⊆ Finset.range B := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpS, hpP⟩ := hp
        rw [Finset.mem_range]
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpS).two_le
        have hppos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
        have hlt : (p : ℝ) < (2 : ℝ) ^ eps⁻¹ := by
          have hbase : (((p : ℝ) ^ eps) ^ eps⁻¹) < (2 : ℝ) ^ eps⁻¹ :=
            Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hppos) eps) hpP (inv_pos.mpr heps)
          rwa [← Real.rpow_mul (le_of_lt hppos) eps eps⁻¹, mul_inv_cancel₀ (ne_of_gt heps),
            Real.rpow_one] at hbase
        have hle : (p : ℝ) ≤ (Nat.ceil ((2 : ℝ) ^ eps⁻¹) : ℝ) :=
          le_trans hlt.le (Nat.le_ceil _)
        have hple : p ≤ Nat.ceil ((2 : ℝ) ^ eps⁻¹) := by exact_mod_cast hle
        rw [hB]; omega
      calc (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card
          ≤ (Finset.range B).card := Finset.card_le_card hsub
        _ = B := Finset.card_range B
    calc (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
            ((n.factorization p + 1 : ℕ) : ℝ))
          * (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ^ eps < 2),
              ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ (K ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card
              * ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
                  (p : ℝ) ^ (eps * (n.factorization p : ℝ)))
            * (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ^ eps < 2),
                (p : ℝ) ^ (eps * (n.factorization p : ℝ))) := by
          apply mul_le_mul hA hBl
          · positivity
          · positivity
      _ = K ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card
            * ((∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2),
                  (p : ℝ) ^ (eps * (n.factorization p : ℝ)))
                * (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ^ eps < 2),
                    (p : ℝ) ^ (eps * (n.factorization p : ℝ)))) := by ring
      _ = K ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card
            * (∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * (n.factorization p : ℝ))) := by
          rw [Finset.prod_filter_mul_prod_filter_not n.primeFactors
                (fun p : ℕ => (p : ℝ) ^ eps < 2)
                (fun p : ℕ => (p : ℝ) ^ (eps * (n.factorization p : ℝ)))]
      _ = K ^ (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ eps < 2)).card * (n : ℝ) ^ eps := by
          rw [prod_primeFactors_rpow n hn0 eps]
      _ ≤ K ^ B * (n : ℝ) ^ eps := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) eps)
          exact pow_le_pow_right₀ hK1 hcard
  simpa only [Nat.cast_add, Nat.cast_one] using key

end Commons.NumberTheory.ArithmeticFunction