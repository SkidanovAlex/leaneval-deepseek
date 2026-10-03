import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.Nat.omega_color_sum_weighted_le
import Submission.Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree

open Finset

namespace Commons.NumberTheory.Sieve

private lemma two_pow_card_rpow (n : ℕ) (K : ℝ) : ((2:ℝ)^n)^K = ((2:ℝ)^K)^n := by
  rw [← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      show ((n:ℝ)) * K = K * (n:ℝ) by ring, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast]

private lemma divisors_card_le_two_pow {d : ℕ} (hd : d ≠ 0) (hsq : Squarefree d) :
    d.divisors.card ≤ 2 ^ d.primeFactors.card := by
  apply Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors
  exact (Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree d hd hsq).symm

private lemma g_le_prod_bound {g : ℕ → ℝ} (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    {C : ℝ} (hCp : ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {d : ℕ} (hd : d ≠ 0) (hsq : Squarefree d) :
    g d ≤ C ^ d.primeFactors.card / (d : ℝ) := by
  rw [Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors g hgmul hg1 hsq]
  have hle1 : ∏ p ∈ d.primeFactors, g p ≤ ∏ p ∈ d.primeFactors, C / (p : ℝ) :=
    Finset.prod_le_prod₀ (fun p hp => hg0 p (Nat.prime_of_mem_primeFactors hp))
      (fun p hp => hCp p (Nat.prime_of_mem_primeFactors hp))
  have hprod : (∏ p ∈ d.primeFactors, C / (p : ℝ)) = C ^ d.primeFactors.card / (d : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, ← Finset.prod_natCast,
        Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree d hd hsq]
  rw [hprod] at hle1
  exact hle1

private lemma term_le {K : ℝ} (hK : 0 ≤ K) {g : ℕ → ℝ}
    (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    {C : ℝ} (hCpos : 0 < C) (hCp : ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {cR : ℝ} (hc : (2:ℝ)^K * C ≤ cR)
    {d : ℕ} (hd1 : 1 ≤ d) (hsq : Squarefree d) :
    ((d.divisors.card : ℝ))^K * g d ≤ cR ^ d.primeFactors.card / (d : ℝ) := by
  have hd0 : d ≠ 0 := by omega
  have hdiv : (d.divisors.card : ℝ) ≤ (2:ℝ) ^ d.primeFactors.card := by
    exact_mod_cast divisors_card_le_two_pow hd0 hsq
  have hbase : 0 ≤ (d.divisors.card : ℝ) := by positivity
  have hdivK : ((d.divisors.card : ℝ))^K ≤ ((2:ℝ)^K)^(d.primeFactors.card) := by
    rw [← two_pow_card_rpow]
    exact Real.rpow_le_rpow hbase hdiv hK
  have hg_le := g_le_prod_bound hg0 hgmul hg1 hCp hd0 hsq
  have hgd_nonneg : 0 ≤ g d := by
    rw [Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors g hgmul hg1 hsq]
    exact Finset.prod_nonneg (fun p hp => hg0 p (Nat.prime_of_mem_primeFactors hp))
  have hBnn : 0 ≤ ((2:ℝ)^K)^(d.primeFactors.card) := by positivity
  calc ((d.divisors.card : ℝ))^K * g d
      ≤ ((2:ℝ)^K)^(d.primeFactors.card) * (C ^ d.primeFactors.card / (d : ℝ)) :=
        mul_le_mul hdivK hg_le hgd_nonneg hBnn
    _ = ((2:ℝ)^K * C) ^ d.primeFactors.card / (d : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← mul_pow]
    _ ≤ cR ^ d.primeFactors.card / (d : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hc _


theorem sum_squarefree_tau_pow_density_le (K : ℝ) (hK : 0 ≤ K) {g : ℕ → ℝ}
    (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hgp : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ x : ℕ, 2 ≤ x →
      (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ K * g d)
        ≤ C₀ * (Real.log (x : ℝ)) ^ K₀ := by
  obtain ⟨C, hCpos, hCp⟩ := hgp
  by_cases hg1 : g 1 = 0
  · refine ⟨1, one_pos, 0, le_refl 0, ?_⟩
    intro x hx
    have hgzero : ∀ d, g d = 0 := by
      intro d
      have h := hgmul d 1 (by simp)
      simp only [Nat.mul_one] at h
      rw [h, hg1, mul_zero]
    have hsum : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ K * g d) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [hgzero d, mul_zero]
    rw [hsum, Real.rpow_zero, mul_one]
    norm_num
  · have hg1' : g 1 = 1 := by
      have h := hgmul 1 1 (by decide)
      simp only [Nat.mul_one] at h
      have h2 : g 1 * 1 = g 1 * g 1 := by rw [mul_one]; exact h
      exact (mul_left_cancel₀ hg1 h2).symm
    let B : ℝ := (2:ℝ)^K * C
    let c : ℕ := ⌊B⌋₊ + 1
    have hBnn : 0 ≤ B := by
      have : 0 < (2:ℝ)^K := Real.rpow_pos_of_pos (by norm_num) K
      exact mul_nonneg (le_of_lt this) (le_of_lt hCpos)
    have hc1 : 1 ≤ c := by simp [c]
    have hcpos_nat : 0 < c := by omega
    have hcR : B ≤ (c:ℝ) := by
      have h1 : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hBnn
      have h2 : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
      simp only [c, Nat.cast_add, Nat.cast_one]
      linarith
    refine ⟨(1 + 1 / Real.log 2) ^ c, by positivity, (c:ℝ), by positivity, ?_⟩
    intro x hx
    have hx1 : 1 < x := by omega
    have hlogx_pos : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast hx1)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogx_ge : Real.log 2 ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have hstepA : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ K * g d)
        ≤ ∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
            (c:ℝ) ^ d.primeFactors.card / (d:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdIcc, hdsq⟩ := hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
      exact term_le hK hg0 hgmul hg1' hCpos hCp hcR hd1 hdsq
    have hstepB : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
            (c:ℝ) ^ d.primeFactors.card / (d:ℝ))
        ≤ ∑ a ∈ Finset.Icc 1 x, (c:ℝ) ^ a.primeFactors.card / (a:ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro a ha _
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        have hac : (0:ℝ) < (c:ℝ) := by exact_mod_cast hcpos_nat
        have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
        positivity
    have hstepC1 : (∑ a ∈ Finset.Icc 1 x, (c:ℝ) ^ a.primeFactors.card / (a:ℝ))
        = ∑ a ∈ Finset.Icc 1 x, (c:ℝ) ^ a.primeFactors.card * Real.rpow (a:ℝ) (-1) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [div_eq_mul_inv]
      congr 1
      exact (Real.rpow_neg_one (a:ℝ)).symm
    have hstepC2 : (∑ a ∈ Finset.Icc 1 x,
            (c:ℝ) ^ a.primeFactors.card * Real.rpow (a:ℝ) (-1))
        ≤ (∑ k ∈ Finset.Icc 1 x, Real.rpow (k:ℝ) (-1)) ^ c :=
      Commons.NumberTheory.Nat.omega_color_sum_weighted_le c x hc1 1 (by norm_num)
    have hharm : (∑ k ∈ Finset.Icc 1 x, Real.rpow (k:ℝ) (-1)) = (harmonic x : ℝ) := by
      have hrw : (harmonic x : ℝ) = ∑ k ∈ Finset.Icc 1 x, (k:ℝ)⁻¹ := by
        rw [harmonic_eq_sum_Icc]; push_cast; rfl
      rw [hrw]
      apply Finset.sum_congr rfl
      intro k hk
      change (k:ℝ) ^ (-(1:ℝ)) = (k:ℝ)⁻¹
      rw [Real.rpow_neg_one]
    have hstepD : (∑ k ∈ Finset.Icc 1 x, Real.rpow (k:ℝ) (-1)) ^ c
        ≤ (1 + Real.log (x:ℝ)) ^ c := by
      apply pow_le_pow_left₀ _ _ c
      · exact Finset.sum_nonneg (fun k hk => Real.rpow_nonneg (by positivity) _)
      · rw [hharm]
        exact harmonic_le_one_add_log x
    have hstepE : (1 + Real.log (x:ℝ)) ^ c
        ≤ (1 + 1 / Real.log 2) ^ c * (Real.log (x:ℝ)) ^ c := by
      have hle : 1 + Real.log (x:ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (x:ℝ) := by
        have hdiv : (1:ℝ) ≤ Real.log (x:ℝ) / Real.log 2 :=
          (le_div_iff₀ hlog2_pos).mpr (by linarith)
        have hdiv' : (1:ℝ) ≤ Real.log (x:ℝ) * (Real.log 2)⁻¹ := by
          rwa [div_eq_mul_inv] at hdiv
        have hexp : (1 + 1 / Real.log 2) * Real.log (x:ℝ)
            = Real.log (x:ℝ) + Real.log (x:ℝ) * (Real.log 2)⁻¹ := by ring
        rw [hexp]; linarith
      calc (1 + Real.log (x:ℝ)) ^ c
          ≤ ((1 + 1 / Real.log 2) * Real.log (x:ℝ)) ^ c :=
            pow_le_pow_left₀ (by positivity) hle c
        _ = (1 + 1 / Real.log 2) ^ c * (Real.log (x:ℝ)) ^ c := mul_pow _ _ _
    calc (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ K * g d)
        ≤ ∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
            (c:ℝ) ^ d.primeFactors.card / (d:ℝ) := hstepA
      _ ≤ ∑ a ∈ Finset.Icc 1 x, (c:ℝ) ^ a.primeFactors.card / (a:ℝ) := hstepB
      _ = ∑ a ∈ Finset.Icc 1 x,
            (c:ℝ) ^ a.primeFactors.card * Real.rpow (a:ℝ) (-1) := hstepC1
      _ ≤ (∑ k ∈ Finset.Icc 1 x, Real.rpow (k:ℝ) (-1)) ^ c := hstepC2
      _ ≤ (1 + Real.log (x:ℝ)) ^ c := hstepD
      _ ≤ (1 + 1 / Real.log 2) ^ c * (Real.log (x:ℝ)) ^ c := hstepE
      _ = (1 + 1 / Real.log 2) ^ c * (Real.log (x:ℝ)) ^ (c:ℝ) := by
            rw [show (Real.log (x:ℝ)) ^ (c:ℝ) = (Real.log (x:ℝ)) ^ c from Real.rpow_natCast _ _]

end Commons.NumberTheory.Sieve