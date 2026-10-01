import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Commons.NumberTheory.Nat

theorem two_pow_omega_le_const_mul_rpow (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (2 : ℝ) ^ (n.primeFactors.card) ≤ C * (n : ℝ) ^ eps := by
  obtain ⟨m, hm_ge⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / eps))
  -- Key estimate: if `p` is at least `2^(1/eps)` then `2 ≤ p^eps`.
  have key : ∀ p : ℕ, (2 : ℝ) ^ (1 / eps) ≤ (p : ℝ) → (2 : ℝ) ≤ (p : ℝ) ^ eps := by
    intro p hp
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hp (le_of_lt heps)
    have heq : ((2 : ℝ) ^ (1 / eps)) ^ eps = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : (1 / eps) * eps = 1 := by
        field_simp
      rw [h1, Real.rpow_one]
    rwa [heq] at h
  let PR : Finset ℕ := (Finset.range (m + 1)).filter Nat.Prime
  refine ⟨(2 : ℝ) ^ (PR.card), by positivity, ?_⟩
  intro n hn
  let P : Finset ℕ := n.primeFactors
  let S : Finset ℕ := P.filter (fun p => p ≤ m)
  let T : Finset ℕ := P.filter (fun p => ¬ p ≤ m)
  change (2 : ℝ) ^ (P.card) ≤ (2 : ℝ) ^ (PR.card) * (n : ℝ) ^ eps
  have hcard : S.card + T.card = P.card := by
    simp only [S, T, P]
    exact Finset.card_filter_add_card_filter_not (s := n.primeFactors) (p := fun q => q ≤ m)
  have hpow : (2 : ℝ) ^ (P.card) = (2 : ℝ) ^ (S.card) * (2 : ℝ) ^ (T.card) := by
    rw [← hcard, pow_add]
  have hSsub : S ⊆ PR := by
    intro p hp
    simp only [S, P, Finset.mem_filter] at hp
    simp only [PR, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hp.2, (Nat.mem_primeFactors.mp hp.1).1⟩
  have hA : (2 : ℝ) ^ (S.card) ≤ (2 : ℝ) ^ (PR.card) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.card_le_card hSsub)
  have hTbound : (2 : ℝ) ^ (T.card) ≤ (n : ℝ) ^ eps := by
    have h1 : (2 : ℝ) ^ (T.card) = ∏ p ∈ T, (2 : ℝ) :=
      (Finset.prod_const (s := T) (2 : ℝ)).symm
    rw [h1]
    calc ∏ p ∈ T, (2 : ℝ) ≤ ∏ p ∈ T, (p : ℝ) ^ eps := by
          apply Finset.prod_le_prod₀
          · intro p hp
            norm_num
          · intro p hp
            simp only [T, P, Finset.mem_filter] at hp
            have hmp : m < p := not_le.mp hp.2
            exact key p (le_trans hm_ge (by exact_mod_cast (le_of_lt hmp)))
      _ ≤ ∏ p ∈ P, (p : ℝ) ^ eps := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀
          · intro p hp
            simp only [T, Finset.mem_filter] at hp
            exact hp.1
          · intro p hp
            positivity
          · intro p hp hpnin
            have hp2 : (1 : ℝ) ≤ (p : ℝ) := by
              have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
              exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hpprime.two_le)
            exact Real.one_le_rpow hp2 (le_of_lt heps)
      _ = (∏ p ∈ P, (p : ℝ)) ^ eps := by
          exact Real.finsetProd_rpow P (fun p => (p : ℝ)) (by intro p hp; positivity) eps
      _ ≤ (n : ℝ) ^ eps := by
          apply Real.rpow_le_rpow (by positivity)
          · have hdvd : (∏ p ∈ P, p) ∣ n := by
              simp only [P]
              exact Nat.prod_primeFactors_dvd n
            have hle : (∏ p ∈ P, p) ≤ n := Nat.le_of_dvd (by omega) hdvd
            rw [← Nat.cast_prod]
            exact_mod_cast hle
          · exact le_of_lt heps
  rw [hpow]
  exact mul_le_mul hA hTbound (by positivity) (by positivity)

end Commons.NumberTheory.Nat