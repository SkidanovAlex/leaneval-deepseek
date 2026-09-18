import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Finite
import Submission.Commons.NumberTheory.DuffinSchaeffer.factorial_succ_le_prod_primeFactors

namespace Commons.NumberTheory.DuffinSchaeffer

theorem eventually_four_pow_primeFactors_card_lt_mul_nat (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in Filter.atTop, (4 : ℝ) ^ n.primeFactors.card < ε * n := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos_real : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  have hNpos_real' : (0 : ℝ) < N := lt_trans hNpos_real hN
  have hNpos : 0 < N := by exact_mod_cast hNpos_real'
  have hεN : (1 : ℝ) < ε * N := (div_lt_iff₀' hε).mp hN
  have hfact_ev : ∀ᶠ k in Filter.atTop, (N:ℕ) * 4 ^ k < Nat.factorial (k - 0) := by
    simpa using (Nat.eventually_mul_pow_lt_factorial_sub N 4 0)
  rcases Filter.eventually_atTop.1 hfact_ev with ⟨K, hK⟩
  have hK' : ∀ k, K ≤ k → (N:ℕ) * 4 ^ k < Nat.factorial k := by
    intro k hk
    simpa using hK k hk
  obtain ⟨B, hB⟩ := exists_nat_gt ((4 : ℝ) ^ K / ε)
  let M : ℕ := max B 1
  refine Filter.eventually_atTop.2 ⟨M, ?_⟩
  intro n hn
  have hnB : B ≤ n := le_trans (Nat.le_max_left B 1) hn
  have hnpos : 0 < n := by
    exact lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right B 1) hn)
  let k : ℕ := n.primeFactors.card
  have hprod_dvd : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have hprod_le_n_nat : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hnpos hprod_dvd
  have hkfac_le_prod_nat : Nat.factorial k ≤ ∏ p ∈ n.primeFactors, p := by
    simpa [k] using (Nat.factorial_le (Nat.le_succ n.primeFactors.card)).trans
      (factorial_succ_le_prod_primeFactors n)
  have hkfac_le_n_nat : Nat.factorial k ≤ n := le_trans hkfac_le_prod_nat hprod_le_n_nat
  have hkfac_le_n : (Nat.factorial k : ℝ) ≤ n := by exact_mod_cast hkfac_le_n_nat
  by_cases hk_small : k < K
  · have h4k_le_4K : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ K := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Nat.le_of_lt hk_small)
    have h4K_lt_εB : (4 : ℝ) ^ K < ε * B := by
      have hdiv : (4 : ℝ) ^ K / ε < (B : ℝ) := by exact_mod_cast hB
      exact (div_lt_iff₀' hε).mp hdiv
    have hεB_le_εn : ε * (B : ℝ) ≤ ε * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnB) hε.le
    exact lt_of_lt_of_le (lt_of_le_of_lt h4k_le_4K h4K_lt_εB) hεB_le_εn
  · have hklarge : K ≤ k := le_of_not_gt hk_small
    have hnat : (N:ℕ) * 4 ^ k < Nat.factorial k := hK' k hklarge
    have hreal_nat : (N : ℝ) * (4 : ℝ) ^ k < (Nat.factorial k : ℝ) := by
      have hcast : (((N:ℕ) * 4 ^ k : ℕ) : ℝ) < Nat.factorial k := by exact_mod_cast hnat
      simpa [Nat.cast_mul, Nat.cast_pow] using hcast
    have hstep1 : (4 : ℝ) ^ k < ε * (N : ℝ) * (4 : ℝ) ^ k := by
      have h := mul_lt_mul_of_pos_right hεN (pow_pos (by norm_num : (0 : ℝ) < 4) k)
      simpa [one_mul] using h
    have hstep2 : ε * (N : ℝ) * (4 : ℝ) ^ k < ε * (Nat.factorial k : ℝ) := by
      have h := mul_lt_mul_of_pos_left hreal_nat hε
      simpa [mul_assoc] using h
    have hstep3 : ε * (Nat.factorial k : ℝ) ≤ ε * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_left hkfac_le_n hε.le
    exact lt_of_lt_of_le (hstep1.trans hstep2) hstep3

end Commons.NumberTheory.DuffinSchaeffer