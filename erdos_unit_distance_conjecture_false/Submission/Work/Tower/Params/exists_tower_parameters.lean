import Mathlib
import Submission.Work.Defs.Basic

namespace Work.Tower.Params

theorem exists_tower_parameters
    (C_A : ℝ) (hCA : 0 < C_A)
    (hap : ∀ ℓ : ℕ, ∃ r : Fin ℓ → ℕ, (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧
        (∀ i, r i % 3 = 1) ∧ (∑ i, Real.log (r i : ℝ)) ≤ C_A * (ℓ : ℝ) * Real.log ℓ + C_A)
    (H : ℝ) (hH : 0 < H) (C₀ : ℕ) :
    ∃ (ℓ : ℕ) (r : Fin ℓ → ℕ) (t : ℕ) (C : ℝ),
      (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧ (∀ i, r i % 3 = 1) ∧
      0 < ℓ ∧ 0 < t ∧ 1 ≤ C ∧
      C = max 1 (2 * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ))) ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      4 * (((ℓ - 1 : ℕ) : ℝ) + C₀ + 3 * t) < (((ℓ - 1 : ℕ) : ℝ)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- Constants
  set K : ℝ := Real.log 2 + (2 / 3) * C_A with hK_def
  have hK : 0 < K := by rw [hK_def]; linarith [hlog2, hCA.le]
  set K₁ : ℝ := 1 + 4 * K with hK₁_def
  have hK₁pos : 0 < K₁ := by rw [hK₁_def]; linarith [hK]
  have hK₁ge1 : 1 ≤ K₁ := by rw [hK₁_def]; linarith [hK.le]
  have hlogK₁ : 0 ≤ Real.log K₁ := Real.log_nonneg hK₁ge1
  set K₂ : ℝ := |Real.log H| + Real.log K₁ + 3 + 4 * K with hK₂_def
  have hK₂ : 0 < K₂ := by rw [hK₂_def]; linarith [abs_nonneg (Real.log H), hlogK₁, hK]
  set A : ℝ := K₂ / Real.log 2 with hA_def
  have hA : 0 < A := by rw [hA_def]; exact div_pos hK₂ hlog2
  set B : ℝ := 28 + 4 * (C₀ : ℝ) + 24 * A with hB_def
  have hB : 0 < B := by rw [hB_def]; have hc₀ : (0 : ℝ) ≤ (C₀ : ℝ) := Nat.cast_nonneg C₀; linarith [hA.le]
  set M : ℝ := 4 * B with hM_def
  have hM : 0 < M := by rw [hM_def]; linarith [hB]
  -- Choose m large
  set m : ℕ := ⌈M⌉₊ + 1 with hm_def
  have hmcast : (m : ℝ) = (⌈M⌉₊ : ℝ) + 1 := by rw [hm_def, Nat.cast_add, Nat.cast_one]
  have hmM : (M : ℝ) < m := by rw [hmcast]; linarith [Nat.le_ceil M]
  have hm2 : 2 ≤ m := by
    have h1 : 1 ≤ ⌈M⌉₊ := Nat.ceil_pos.mpr hM
    rw [hm_def]; omega
  have hm1n : 1 ≤ m := by omega
  have hmpos_nat : 0 < m := by omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1n
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmposr : (0 : ℝ) < (m : ℝ) := by linarith
  have hm3ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ hm1
  have hm2ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm1
  have hm2m3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ hm1 (show 2 ≤ 3 by norm_num)
  have hm_m3 : (m : ℝ) ≤ (m : ℝ) ^ 3 := by
    calc (m : ℝ) = (m : ℝ) * 1 := by ring
    _ ≤ (m : ℝ) * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hm2ge1 hmposr.le
    _ = (m : ℝ) ^ 3 := by ring
  have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) := by
    have := Real.log_le_sub_one_of_pos hmposr; linarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
  -- Set ℓ = m²
  set ℓ : ℕ := m ^ 2 with hℓ_def
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ_def]; exact Nat.one_le_pow 2 m hmpos_nat
  have hℓ1r : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hℓnn : (0 : ℝ) ≤ (ℓ : ℝ) := by linarith
  have hcastℓ : (ℓ : ℝ) = (m : ℝ) ^ 2 := by rw [hℓ_def, Nat.cast_pow]
  have hlogℓ' : Real.log ((m : ℝ) ^ 2) = 2 * Real.log (m : ℝ) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogℓ0 : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg hℓ1r
  have hL : (0 : ℝ) ≤ (ℓ : ℝ) * Real.log ℓ + 1 := by
    have := mul_nonneg hℓnn hlogℓ0; linarith
  have hℓlog : (ℓ : ℝ) * Real.log ℓ ≤ 2 * (m : ℝ) ^ 3 := by
    rw [hcastℓ, hlogℓ']
    calc (m : ℝ) ^ 2 * (2 * Real.log (m : ℝ)) ≤ (m : ℝ) ^ 2 * (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [hlogm]) (sq_nonneg _)
    _ = 2 * (m : ℝ) ^ 3 := by ring
  -- Get the primes
  obtain ⟨r, hrp, hri, hrm, hrsum⟩ := hap ℓ
  set S : ℝ := ∑ i, Real.log (r i : ℝ) with hS_def
  have hSbound : S ≤ C_A * ((ℓ : ℝ) * Real.log ℓ + 1) := by
    calc S ≤ C_A * (ℓ : ℝ) * Real.log ℓ + C_A := hrsum
    _ = C_A * ((ℓ : ℝ) * Real.log ℓ + 1) := by ring
  set E : ℝ := 2 * Real.exp ((2 / 3) * S) with hE_def
  set C : ℝ := max 1 E with hC_def
  have hC1 : 1 ≤ C := by rw [hC_def]; exact le_max_left 1 E
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC1
  have h1logC : 0 < 1 + Real.log C := by linarith
  have hlogC_le : Real.log C ≤ Real.log 2 + (2 / 3) * C_A * ((ℓ : ℝ) * Real.log ℓ + 1) := by
    rcases le_or_gt 1 E with hE1 | hE1
    · have hmax : max 1 E = E := max_eq_right hE1
      have hthis : Real.log C = Real.log 2 + (2 / 3) * S := by
        rw [hC_def, hmax, hE_def, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
          Real.log_exp]
      rw [hthis]
      have hb : (2 / 3) * S ≤ (2 / 3) * (C_A * ((ℓ : ℝ) * Real.log ℓ + 1)) :=
        mul_le_mul_of_nonneg_left hSbound (by norm_num)
      linarith
    · have hmax : max 1 E = 1 := max_eq_left hE1.le
      rw [hC_def, hmax, Real.log_one]
      exact add_nonneg hlog2.le (mul_nonneg (mul_nonneg (by norm_num) hCA.le) hL)
  have hlogC_le2 : Real.log C ≤ K * ((ℓ : ℝ) * Real.log ℓ + 2) := by
    have h1 : Real.log 2 ≤ K := by rw [hK_def]; linarith [hCA.le]
    have h23K : (2 / 3 : ℝ) * C_A ≤ K := by rw [hK_def]; linarith [hlog2.le]
    have h2 : (2 / 3) * C_A * ((ℓ : ℝ) * Real.log ℓ + 1) ≤ K * ((ℓ : ℝ) * Real.log ℓ + 1) :=
      mul_le_mul_of_nonneg_right h23K hL
    calc Real.log C ≤ Real.log 2 + (2 / 3) * C_A * ((ℓ : ℝ) * Real.log ℓ + 1) := hlogC_le
    _ ≤ K + K * ((ℓ : ℝ) * Real.log ℓ + 1) := add_le_add h1 h2
    _ = K * ((ℓ : ℝ) * Real.log ℓ + 2) := by ring
  have hlogC_le3 : Real.log C ≤ 4 * K * (m : ℝ) ^ 3 := by
    have h1 : (ℓ : ℝ) * Real.log ℓ + 2 ≤ 2 * (m : ℝ) ^ 3 + 2 := by linarith [hℓlog]
    have h3 : 2 * (m : ℝ) ^ 3 + 2 ≤ 4 * (m : ℝ) ^ 3 := by linarith [hm3ge1]
    calc Real.log C ≤ K * ((ℓ : ℝ) * Real.log ℓ + 2) := hlogC_le2
    _ ≤ K * (2 * (m : ℝ) ^ 3 + 2) := mul_le_mul_of_nonneg_left h1 hK.le
    _ ≤ K * (4 * (m : ℝ) ^ 3) := mul_le_mul_of_nonneg_left h3 hK.le
    _ = 4 * K * (m : ℝ) ^ 3 := by ring
  have h1logC_le : 1 + Real.log C ≤ K₁ * (m : ℝ) ^ 3 := by
    calc 1 + Real.log C ≤ 1 + 4 * K * (m : ℝ) ^ 3 := by linarith [hlogC_le3]
    _ ≤ (m : ℝ) ^ 3 + 4 * K * (m : ℝ) ^ 3 := by linarith [hm3ge1]
    _ = K₁ * (m : ℝ) ^ 3 := by rw [hK₁_def]; ring
  have hlog1logC : Real.log (1 + Real.log C) ≤ Real.log K₁ + 3 * (m : ℝ) ^ 3 := by
    have hm3pos : (0 : ℝ) < (m : ℝ) ^ 3 := pow_pos hmposr 3
    have h2 : Real.log (K₁ * (m : ℝ) ^ 3) = Real.log K₁ + 3 * Real.log (m : ℝ) := by
      rw [Real.log_mul (ne_of_gt hK₁pos) (ne_of_gt hm3pos), Real.log_pow]; push_cast; ring
    have h1 : Real.log (1 + Real.log C) ≤ Real.log (K₁ * (m : ℝ) ^ 3) :=
      Real.log_le_log h1logC h1logC_le
    have h3 : 3 * Real.log (m : ℝ) ≤ 3 * (m : ℝ) ^ 3 := by linarith [hlogm, hm_m3]
    rw [h2] at h1
    linarith [h1, h3]
  -- X and its log
  set X : ℝ := H * C * (1 + Real.log C) with hX_def
  have hX : 0 < X := by
    rw [hX_def]; exact mul_pos (mul_pos hH hCpos) h1logC
  have hXeq : Real.log X = Real.log H + Real.log C + Real.log (1 + Real.log C) := by
    rw [hX_def, Real.log_mul (ne_of_gt (mul_pos hH hCpos)) (ne_of_gt h1logC),
      Real.log_mul (ne_of_gt hH) (ne_of_gt hCpos)]
  have hlogX : Real.log X ≤ K₂ * (m : ℝ) ^ 3 := by
    have h4 : Real.log H ≤ |Real.log H| * (m : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hm3ge1 (abs_nonneg (Real.log H))
      rw [mul_one] at h
      exact le_trans (le_abs_self _) h
    have hK₁m3 : Real.log K₁ ≤ Real.log K₁ * (m : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hm3ge1 hlogK₁
      rwa [mul_one] at h
    have e : K₂ * (m : ℝ) ^ 3 =
        |Real.log H| * (m : ℝ) ^ 3 + Real.log K₁ * (m : ℝ) ^ 3 + 3 * (m : ℝ) ^ 3
          + 4 * K * (m : ℝ) ^ 3 := by rw [hK₂_def]; ring
    rw [hXeq, e]
    linarith [h4, hlogC_le3, hlog1logC, hK₁m3]
  set y : ℝ := 2 * Real.logb 2 X with hy_def
  have hlogbX : Real.logb 2 X ≤ A * (m : ℝ) ^ 3 := by
    have hrfl : Real.logb 2 X = Real.log X / Real.log 2 := rfl
    rw [hrfl, hA_def, div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hlog2).mpr hlogX
  -- t
  set t : ℕ := ⌈y⌉₊ + 1 with ht_def
  have ht_pos : 0 < t := by rw [ht_def]; omega
  have htc : (t : ℝ) = (⌈y⌉₊ : ℝ) + 1 := by rw [ht_def, Nat.cast_add, Nat.cast_one]
  have ht_upper : (t : ℝ) ≤ 2 * A * (m : ℝ) ^ 3 + 2 := by
    rcases le_or_gt 0 y with hy | hy
    · have h2 : y ≤ 2 * A * (m : ℝ) ^ 3 := by rw [hy_def]; linarith [hlogbX]
      have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
      rw [htc]; linarith
    · have h0 : ⌈y⌉₊ = 0 := Nat.ceil_eq_zero.mpr hy.le
      have htle : (t : ℝ) = 1 := by rw [ht_def, h0]; norm_num
      have hnn : (0 : ℝ) ≤ 2 * A * (m : ℝ) ^ 3 :=
        mul_nonneg (mul_nonneg (by norm_num) hA.le) (pow_nonneg hmnn 3)
      rw [htle]; linarith
  have hpow : (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t := by
    rw [← hX_def]
    rcases le_or_gt 0 y with hy | hy
    · have h1 : y < (t : ℝ) := by have := Nat.le_ceil y; rw [htc]; linarith
      have h3 : (2 : ℝ) ^ y = X ^ 2 := by
        rw [hy_def, two_mul (Real.logb 2 X), Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hX, pow_two]
      have h2 : (2 : ℝ) ^ t = (2 : ℝ) ^ ((t : ℝ)) := (Real.rpow_natCast 2 t).symm
      rw [h2, ← h3]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
    · have h0 : ⌈y⌉₊ = 0 := Nat.ceil_eq_zero.mpr hy.le
      have ht1 : t = 1 := by rw [ht_def, h0]
      have hy2 : Real.logb 2 X < 0 := by rw [hy_def] at hy; linarith
      have hX1 : X < 1 := by
        have hr := Real.rpow_logb (show (0 : ℝ) < 2 by norm_num)
          (show (2 : ℝ) ≠ 1 by norm_num) hX
        have hlt : (2 : ℝ) ^ (Real.logb 2 X) < (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hy2
        rw [Real.rpow_zero] at hlt
        rwa [hr] at hlt
      have hX2 : X ^ 2 < 1 := pow_lt_one₀ hX.le hX1 (by norm_num : (2 : ℕ) ≠ 0)
      rw [ht1]
      have hp1 : (2 : ℝ) ^ (1 : ℕ) = 2 := pow_one 2
      rw [hp1]
      linarith [hX2]
  have hfinal : 4 * (((ℓ - 1 : ℕ) : ℝ) + C₀ + 3 * t) < (((ℓ - 1 : ℕ) : ℝ)) ^ 2 := by
    have hcast : ((ℓ - 1 : ℕ) : ℝ) = (m : ℝ) ^ 2 - 1 := by
      rw [Nat.cast_sub hℓ1, hℓ_def]; push_cast; ring
    rw [hcast]
    have hm2ge4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hm2r 2
    have hsq : (m : ℝ) ^ 4 / 4 ≤ ((m : ℝ) ^ 2 - 1) ^ 2 := by
      have h : (m : ℝ) ^ 2 / 2 ≤ (m : ℝ) ^ 2 - 1 := by linarith
      calc (m : ℝ) ^ 4 / 4 = ((m : ℝ) ^ 2 / 2) ^ 2 := by ring
      _ ≤ ((m : ℝ) ^ 2 - 1) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have hC0nn : (0 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast Nat.zero_le C₀
    have hC0m3 : (C₀ : ℝ) ≤ (C₀ : ℝ) * (m : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hm3ge1 hC0nn
      rwa [mul_one] at h
    have h24 : (24 : ℝ) ≤ 24 * (m : ℝ) ^ 3 := by linarith [hm3ge1]
    have hLHS : 4 * ((m : ℝ) ^ 2 - 1 + (C₀ : ℝ) + 3 * (t : ℝ)) ≤ B * (m : ℝ) ^ 3 := by
      calc 4 * ((m : ℝ) ^ 2 - 1 + (C₀ : ℝ) + 3 * (t : ℝ))
          ≤ 4 * (m : ℝ) ^ 2 + 4 * (C₀ : ℝ) + 12 * (t : ℝ) := by linarith
      _ ≤ 4 * (m : ℝ) ^ 3 + 4 * (C₀ : ℝ) * (m : ℝ) ^ 3 + 24 * A * (m : ℝ) ^ 3
            + 24 * (m : ℝ) ^ 3 := by linarith [hm2m3, hC0m3, ht_upper, h24]
      _ = B * (m : ℝ) ^ 3 := by rw [hB_def]; ring
    have hBlt : B * (m : ℝ) ^ 3 < (m : ℝ) ^ 4 / 4 := by
      have hm3pos : (0 : ℝ) < (m : ℝ) ^ 3 := pow_pos hmposr 3
      have h1 : B < (m : ℝ) / 4 := by
        have h := hmM
        rw [hM_def] at h
        linarith
      calc B * (m : ℝ) ^ 3 < ((m : ℝ) / 4) * (m : ℝ) ^ 3 := mul_lt_mul_of_pos_right h1 hm3pos
      _ = (m : ℝ) ^ 4 / 4 := by ring
    linarith [hLHS, hsq, hBlt]
  refine ⟨ℓ, r, t, C, hrp, hri, hrm, ?_, ht_pos, hC1, ?_, hpow, hfinal⟩
  · rw [hℓ_def]; exact pow_pos hmpos_nat 2
  · rw [hC_def, hE_def, hS_def]

end Work.Tower.Params
