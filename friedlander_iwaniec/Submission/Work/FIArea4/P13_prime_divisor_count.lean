import Mathlib

namespace Work.FIArea4

open Finset

/-- For `n ≠ 0`, the number of *distinct* prime factors of `n` is at most `log₂ n`:
`2 ^ (n.primeFactors.card) ≤ n`.  This is because `n` is the product of `p ^ (n.factorization p)`
over the primes `p ∣ n`, each factor being at least `2`. -/
lemma fi_two_pow_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have h1 : 1 ≤ n.factorization p := (hpp.dvd_iff_one_le_factorization hn).mp hpdvd
  calc 2 ≤ p := hpp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hpp.one_le h1

/-- A finset `T` of primes each dividing `n ≠ 0` has at most `log₂ n` elements:
`2 ^ T.card ≤ n`. -/
lemma fi_two_pow_card_le_of (T : Finset ℕ) (n : ℕ) (hn : n ≠ 0)
    (hT : ∀ p ∈ T, p.Prime) (hdvd : ∀ p ∈ T, p ∣ n) : 2 ^ T.card ≤ n := by
  have hsub : T ⊆ n.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨hT p hp, hdvd p hp, hn⟩
  calc 2 ^ T.card ≤ 2 ^ n.primeFactors.card :=
        Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card hsub)
    _ ≤ n := fi_two_pow_card_primeFactors_le n hn

theorem P13_prime_divisor_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S N r : ℕ), 1 ≤ R → 1 ≤ S → 1 ≤ r → r ≤ 2 * R →
      ((((Finset.Ioc N (2 * N)).filter Nat.Prime).filter (fun p => p ∣ r)).card : ℝ)
        ≤ C * ((R : ℝ) * (S : ℝ)) ^ ε := by
  refine ⟨(Real.log 2 + 1 / ε) / Real.log 2, ?_, ?_⟩
  · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_pos (add_pos hlog2pos (one_div_pos.mpr hε)) hlog2pos
  · intro R S N r hR hS hr hr2R
    set T := ((Finset.Ioc N (2 * N)).filter Nat.Prime).filter (fun p => p ∣ r) with hTdef
    have hTprime : ∀ p ∈ T, p.Prime := by
      intro p hp; rw [hTdef] at hp; simp only [Finset.mem_filter] at hp; exact hp.1.2
    have hTdvd : ∀ p ∈ T, p ∣ r := by
      intro p hp; rw [hTdef] at hp; simp only [Finset.mem_filter] at hp; exact hp.2
    have hrne : r ≠ 0 := by omega
    have h2 : 2 ^ T.card ≤ r := fi_two_pow_card_le_of T r hrne hTprime hTdvd
    have h2R : (2 : ℝ) ^ T.card ≤ (r : ℝ) := by
      have := Nat.cast_le (α := ℝ) |>.mpr h2
      simpa using this
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog1 : (T.card : ℝ) * Real.log 2 ≤ Real.log (r : ℝ) := by
      have := Real.log_le_log (show (0:ℝ) < (2:ℝ) ^ T.card by positivity) h2R
      rwa [Real.log_pow] at this
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hRpos : (0:ℝ) < (R:ℝ) := lt_of_lt_of_le one_pos hR1
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hlogr_le : Real.log (r : ℝ) ≤ Real.log (2 * (R : ℝ)) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hr2R
    have hlog_mul : Real.log (2 * (R : ℝ)) = Real.log 2 + Real.log (R : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    have hlogR : Real.log (R:ℝ) ≤ (R:ℝ)^ε / ε := Real.log_natCast_le_rpow_div R hε
    have hone : (1:ℝ) ≤ (R:ℝ)^ε := Real.one_le_rpow hR1 hε.le
    have hlog2b : Real.log 2 ≤ Real.log 2 * (R:ℝ)^ε :=
      le_mul_of_one_le_right hlog2pos.le hone
    have hsum : Real.log 2 + Real.log (R:ℝ) ≤ (Real.log 2 + 1/ε) * (R:ℝ)^ε := by
      have hkey : (Real.log 2 + 1/ε) * (R:ℝ)^ε
          = Real.log 2 * (R:ℝ)^ε + (R:ℝ)^ε / ε := by
        rw [div_eq_mul_inv]; ring
      rw [hkey]; exact add_le_add hlog2b hlogR
    have hRS : (R:ℝ)^ε ≤ ((R:ℝ) * (S:ℝ))^ε := by
      apply Real.rpow_le_rpow (le_of_lt hRpos)
      · exact le_mul_of_one_le_right (le_of_lt hRpos) hS1
      · exact hε.le
    have hbound : (T.card : ℝ) * Real.log 2
        ≤ (Real.log 2 + 1/ε) * ((R:ℝ)*(S:ℝ))^ε := by
      have step5 : (Real.log 2 + 1/ε) * (R:ℝ)^ε
          ≤ (Real.log 2 + 1/ε) * ((R:ℝ)*(S:ℝ))^ε := by
        apply mul_le_mul_of_nonneg_left hRS
        have : (0:ℝ) < Real.log 2 + 1/ε := add_pos hlog2pos (one_div_pos.mpr hε)
        linarith
      linarith [hlog1, hlogr_le, hlog_mul.le, hsum, step5]
    have hgoal : (T.card : ℝ) ≤ ((Real.log 2 + 1/ε)/Real.log 2) * ((R:ℝ)*(S:ℝ))^ε := by
      have heq : ((Real.log 2 + 1/ε)/Real.log 2) * ((R:ℝ)*(S:ℝ))^ε
          = ((Real.log 2 + 1/ε) * ((R:ℝ)*(S:ℝ))^ε)/Real.log 2 := by
        rw [div_mul_eq_mul_div]
      rw [heq, le_div_iff₀ hlog2pos]
      exact hbound
    exact hgoal

end Work.FIArea4
