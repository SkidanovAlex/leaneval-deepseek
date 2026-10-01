import Mathlib

namespace Work.ZeroFreeTables.OffAxis

open Finset


private lemma omega_le_mul_log_aux (a : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n.primeFactors.card : ℝ) ≤ a * Real.log (n : ℝ) := by
  obtain ⟨B0, hB0⟩ := exists_nat_gt (Real.exp (4 / a))
  set B : ℕ := max 2 (B0 + 1) with hBdef
  have hB2 : 2 ≤ B := le_max_left _ _
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hBgt : Real.exp (4 / a) < (B : ℝ) := by
    have hle : (B0 : ℝ) + 1 ≤ (B : ℝ) := by
      exact_mod_cast (le_max_right 2 (B0 + 1))
    linarith [hB0]
  have hlogB : 4 / a ≤ Real.log (B : ℝ) := by
    rw [← Real.log_exp (4 / a)]
    exact Real.log_le_log (Real.exp_pos _) (le_of_lt hBgt)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (Real.exp (2 * ((B : ℝ) + 1) / a))
  refine ⟨max 3 N0, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := le_trans (le_max_left 3 N0) hn
  have hnN0 : N0 ≤ n := le_trans (le_max_right 3 N0) hn
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogexp : 2 * ((B : ℝ) + 1) / a ≤ Real.log (n : ℝ) := by
    have hlt : Real.exp (2 * ((B : ℝ) + 1) / a) < (n : ℝ) := by
      have hc : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN0
      linarith [hN0]
    have h := Real.log_le_log (Real.exp_pos _) (le_of_lt hlt)
    rwa [Real.log_exp] at h
  have hsmall_le : ((B : ℝ) + 1) ≤ (a / 2) * Real.log (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogexp (by positivity : (0 : ℝ) ≤ a / 2)
    have heq : (a / 2) * (2 * ((B : ℝ) + 1) / a) = (B : ℝ) + 1 := by
      field_simp
    rwa [heq] at h
  have hlogprod : Real.log (∏ p ∈ n.primeFactors, (p : ℝ))
      = ∑ p ∈ n.primeFactors, Real.log (p : ℝ) :=
    Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)))
  have hprod_pos : 0 < ∏ p ∈ n.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  have hprod_le : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ (n : ℝ) := by
    have hle : (∏ p ∈ n.primeFactors, p) ≤ n :=
      Nat.le_of_dvd (show 0 < n by omega) (Nat.prod_primeFactors_dvd n)
    calc (∏ p ∈ n.primeFactors, (p : ℝ))
        = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) := by exact_mod_cast hle
  have hsum_le : ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← hlogprod]
    exact Real.log_le_log hprod_pos hprod_le
  have hLmul : ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) * Real.log (B : ℝ)
      ≤ Real.log (n : ℝ) := by
    have h1 : ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ B), Real.log (B : ℝ)
        ≤ ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ B), Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      simp only [Finset.mem_filter] at hp
      have hpgt : B < p := lt_of_not_ge hp.2
      exact Real.log_le_log hBpos (by exact_mod_cast (le_of_lt hpgt))
    have h2 : ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ B), Real.log (p : ℝ)
        ≤ ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      exact Real.log_nonneg (by
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        exact_mod_cast (show 1 ≤ p by omega))
    have h3 : ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ B), Real.log (B : ℝ)
        = ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) * Real.log (B : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h3] at h1
    linarith
  have hL_bd : ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ)
      ≤ (a / 4) * Real.log (n : ℝ) := by
    have h4a : 0 < 4 / a := by positivity
    have hstep : ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) * (4 / a)
        ≤ Real.log (n : ℝ) := by
      calc ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) * (4 / a)
          ≤ ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) * Real.log (B : ℝ) :=
            mul_le_mul_of_nonneg_left hlogB (by positivity)
        _ ≤ Real.log (n : ℝ) := hLmul
    have hd := (le_div_iff₀ h4a).mpr hstep
    have heq : Real.log (n : ℝ) / (4 / a) = (a / 4) * Real.log (n : ℝ) := by
      rw [div_eq_mul_inv, inv_div]; ring
    rwa [heq] at hd
  have hsmall_card : ((n.primeFactors.filter (fun p => p ≤ B)).card : ℝ) ≤ (B : ℝ) + 1 := by
    have hcardn : (n.primeFactors.filter (fun p => p ≤ B)).card ≤ B + 1 := by
      calc (n.primeFactors.filter (fun p => p ≤ B)).card
          ≤ (Finset.range (B + 1)).card := by
            apply Finset.card_le_card
            intro p hp
            simp only [Finset.mem_filter] at hp
            simp only [Finset.mem_range]
            omega
        _ = B + 1 := Finset.card_range _
    have hc : ((n.primeFactors.filter (fun p => p ≤ B)).card : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcardn
    simpa using hc
  have hcard_split : (n.primeFactors.filter (fun p => p ≤ B)).card
      + (n.primeFactors.filter (fun p => ¬ p ≤ B)).card = n.primeFactors.card :=
    Finset.card_filter_add_card_filter_not (s := n.primeFactors) (fun p => p ≤ B)
  have hcard : (n.primeFactors.card : ℝ)
      = ((n.primeFactors.filter (fun p => p ≤ B)).card : ℝ)
        + ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) := by
    rw [← hcard_split]; push_cast; ring
  calc (n.primeFactors.card : ℝ)
      = ((n.primeFactors.filter (fun p => p ≤ B)).card : ℝ)
        + ((n.primeFactors.filter (fun p => ¬ p ≤ B)).card : ℝ) := hcard
    _ ≤ ((B : ℝ) + 1) + (a / 4) * Real.log (n : ℝ) := add_le_add hsmall_card hL_bd
    _ ≤ (a / 2) * Real.log (n : ℝ) + (a / 4) * Real.log (n : ℝ) :=
          add_le_add hsmall_le le_rfl
    _ = (3 * a / 4) * Real.log (n : ℝ) := by ring
    _ ≤ a * Real.log (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hlogn_nonneg
          linarith

private lemma logLogSq_le_mul_log_aux (a : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Real.log (Real.log (n : ℝ)))^2 ≤ a * Real.log (n : ℝ) := by
  set T : ℝ := max 1 (256 / a ^ 2) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT2 : 256 / a ^ 2 ≤ T := le_max_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp T)
  refine ⟨N, ?_⟩
  intro n hn
  have hlt : Real.exp T < (n : ℝ) := by
    have hc : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [hN]
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith [Real.exp_pos T, hlt]
  have ht_ge_T : T ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos T) (le_of_lt hlt)
    rwa [Real.log_exp] at h
  set t : ℝ := Real.log (n : ℝ) with htdef
  have ht1 : 1 ≤ t := le_trans hT1 ht_ge_T
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  set s : ℝ := Real.sqrt t with hsdef
  have hs1 : 1 ≤ s := by
    rw [hsdef, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hst : s ^ 2 = t := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt htpos)
  have hlogt : Real.log t = 2 * Real.log s := by
    rw [← hst, Real.log_pow]; push_cast; ring
  have hlogs_le : Real.log s ≤ 2 * Real.sqrt s := by
    have h := Real.log_le_rpow_div (le_of_lt hspos) (by norm_num : (0 : ℝ) < 1 / 2)
    have heq : s ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * Real.sqrt s := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv]; ring
    rwa [heq] at h
  have hls : (Real.log s) ^ 2 ≤ 4 * s := by
    have h := pow_le_pow_left₀ (Real.log_nonneg hs1) hlogs_le 2
    rw [mul_pow, Real.sq_sqrt (le_of_lt hspos)] at h
    norm_num at h
    exact h
  have h2ls : (2 * Real.log s) ^ 2 ≤ 16 * s := by
    have h := mul_le_mul_of_nonneg_left hls (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2)
    calc (2 * Real.log s) ^ 2 = (2 : ℝ) ^ 2 * (Real.log s) ^ 2 := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ 2 * (4 * s) := h
      _ = 16 * s := by ring
  have hs_ge : 16 / a ≤ s := by
    have h16 : (16 / a) ^ 2 ≤ t := by
      have hsq : (16 / a) ^ 2 = 256 / a ^ 2 := by ring
      rw [hsq, htdef]
      exact le_trans hT2 ht_ge_T
    have hs := Real.sqrt_le_sqrt h16
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 16 / a)] at hs
    rw [hsdef]
    exact hs
  have h16s : 16 * s ≤ a * t := by
    have has16 : 16 ≤ a * s := by
      have h := mul_le_mul_of_nonneg_left hs_ge (le_of_lt ha)
      have heq : a * (16 / a) = 16 := by field_simp
      rwa [heq] at h
    calc 16 * s ≤ (a * s) * s := mul_le_mul_of_nonneg_right has16 (le_of_lt hspos)
      _ = a * t := by rw [← hst]; ring
  calc (Real.log (Real.log (n : ℝ))) ^ 2 = (Real.log t) ^ 2 := by rw [htdef]
    _ = (2 * Real.log s) ^ 2 := by rw [hlogt]
    _ ≤ 16 * s := h2ls
    _ ≤ a * t := h16s
    _ = a * Real.log (n : ℝ) := by rw [htdef]

theorem error_absorb (C f₀ ε : ℝ) (hC : 0 < C) (hf₀ : 0 < f₀) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q : ℝ))) ^ 2)
        ≤ f₀ * ε * Real.log (q : ℝ) := by
  set δ : ℝ := f₀ * ε / C with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨N1, h1⟩ := omega_le_mul_log_aux (δ / 2) (by positivity)
  obtain ⟨N2, h2⟩ := logLogSq_le_mul_log_aux (δ / 2) (by positivity)
  refine ⟨max N1 N2, ?_⟩
  intro q hq
  have hq1 : N1 ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : N2 ≤ q := le_trans (le_max_right _ _) hq
  have b1 := h1 q hq1
  have b2 := h2 q hq2
  have hsum : (q.primeFactors.card : ℝ) + (Real.log (Real.log (q : ℝ))) ^ 2
      ≤ δ * Real.log (q : ℝ) := by
    have h := add_le_add b1 b2
    rwa [show δ / 2 * Real.log (q : ℝ) + δ / 2 * Real.log (q : ℝ)
        = δ * Real.log (q : ℝ) by ring] at h
  calc C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q : ℝ))) ^ 2)
      ≤ C * (δ * Real.log (q : ℝ)) := mul_le_mul_of_nonneg_left hsum (le_of_lt hC)
    _ = f₀ * ε * Real.log (q : ℝ) := by
          rw [hδ]
          field_simp


end Work.ZeroFreeTables.OffAxis
