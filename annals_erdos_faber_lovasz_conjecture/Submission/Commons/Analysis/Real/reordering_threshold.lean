import Mathlib.Analysis.Real.Sqrt

namespace Commons.Analysis.Real

open Filter

theorem reordering_threshold {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 10000) :
    ∃ R : ℕ, ∀ r : ℝ, (R : ℝ) ≤ r →
      (0 < 1 - τ - 7 * Real.sqrt (Real.sqrt τ)) ∧
      (1 ≤ τ * (r - 1)) ∧
      (1 ≤ Real.sqrt (Real.sqrt τ) * (r - 1)) ∧
      (1 + Real.sqrt τ ≤ r / 2) ∧
      (2 * (1 + Real.sqrt τ) ≤ Real.sqrt τ * r) ∧
      (1 ≤ (3 * Real.sqrt (Real.sqrt τ) - Real.sqrt τ) * r ^ 2) ∧
      ((1 - τ - 2 * Real.sqrt τ) * (1 - 1 / r) ≥ 1 - τ - 7 * Real.sqrt (Real.sqrt τ)) := by
  set t := Real.sqrt τ with ht_def
  set s := Real.sqrt t with hs_def
  have ht_pos : 0 < t := by rw [ht_def]; exact Real.sqrt_pos_of_pos hτ0
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hs_pos : 0 < s := by rw [hs_def]; exact Real.sqrt_pos_of_pos ht_pos
  have hτ_le_one : τ ≤ 1 := by linarith
  have ht_le_one : t ≤ 1 := by rw [ht_def]; exact Real.sqrt_le_one.mpr hτ_le_one
  have ht_sq : t ^ 2 = τ := by rw [ht_def]; exact Real.sq_sqrt (le_of_lt hτ0)
  have hτ_le_t : τ ≤ t := by
    have h : t * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_nonneg (by linarith)
    nlinarith [ht_sq, h]
  have ht_le_s : t ≤ s := by
    rw [hs_def, Real.le_sqrt ht_nonneg ht_nonneg]
    have h : t * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_nonneg (by linarith)
    nlinarith [h]
  have ht_le : t ≤ 1 / 100 := by
    rw [ht_def, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have h : ((1 : ℝ) / 100) ^ 2 = 1 / 10000 := by norm_num
    linarith [hτ1, h]
  have hs_le : s ≤ 1 / 10 := by
    rw [hs_def, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have h : ((1 : ℝ) / 10) ^ 2 = 1 / 100 := by norm_num
    linarith [ht_le, h]
  have h1 : 0 < 1 - τ - 7 * s := by linarith [hs_le, hτ1]
  have hc : 0 < 1 - τ - 2 * t := by linarith [ht_le, hτ1]
  have hd : 0 < 7 * s - 2 * t := by linarith [ht_le_s, ht_pos]
  have h3st : 0 < 3 * s - t := by linarith [ht_le_s, ht_pos]
  have hev : ∀ᶠ r in atTop,
      (1 ≤ τ * (r - 1)) ∧ (1 ≤ s * (r - 1)) ∧
      (1 + t ≤ r / 2) ∧ (2 * (1 + t) ≤ t * r) ∧
      (1 ≤ (3 * s - t) * r ^ 2) ∧
      ((1 - τ - 2 * t) * (1 - 1 / r) ≥ 1 - τ - 7 * s) := by
    filter_upwards [eventually_ge_atTop (1 + 1 / τ),
                    eventually_ge_atTop (max 1 (1 / (3 * s - t))),
                    eventually_ge_atTop (2 * (1 + t)),
                    eventually_ge_atTop (2 * (1 + t) / t),
                    eventually_ge_atTop ((1 - τ - 2 * t) / (7 * s - 2 * t))]
      with r hrτ hrmax hr4 hr5 hr7
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 1 ≤ τ * (r - 1)
      have h : 1 / τ ≤ r - 1 := by linarith
      have hle := mul_le_mul_of_nonneg_left h (le_of_lt hτ0)
      have hττ : τ * (1 / τ) = 1 := by rw [mul_one_div, div_self (ne_of_gt hτ0)]
      linarith [hle, hττ]
    · -- 1 ≤ s * (r - 1)
      have hτs : τ ≤ s := le_trans hτ_le_t ht_le_s
      have hs_inv : 1 / s ≤ 1 / τ := one_div_le_one_div_of_le hτ0 hτs
      have h : 1 / s ≤ r - 1 := le_trans hs_inv (by linarith)
      have hle := mul_le_mul_of_nonneg_left h (le_of_lt hs_pos)
      have hss : s * (1 / s) = 1 := by rw [mul_one_div, div_self (ne_of_gt hs_pos)]
      linarith [hle, hss]
    · -- 1 + t ≤ r / 2
      linarith
    · -- 2 * (1 + t) ≤ t * r
      have hle := mul_le_mul_of_nonneg_left hr5 (le_of_lt ht_pos)
      have htd : t * (2 * (1 + t) / t) = 2 * (1 + t) := by
        rw [mul_div_cancel₀ _ (ne_of_gt ht_pos)]
      linarith [hle, htd]
    · -- 1 ≤ (3 * s - t) * r ^ 2
      have hr1' : 1 ≤ r := le_trans (le_max_left _ _) hrmax
      have hr2' : 1 / (3 * s - t) ≤ r := le_trans (le_max_right _ _) hrmax
      have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr1'
      have hrr : r ≤ r ^ 2 := by
        have h : 0 ≤ r * (r - 1) := mul_nonneg hr_nonneg (by linarith)
        nlinarith [h]
      have hstep1 : (3 * s - t) * (1 / (3 * s - t)) ≤ (3 * s - t) * r :=
        mul_le_mul_of_nonneg_left hr2' (le_of_lt h3st)
      have h3inv : (3 * s - t) * (1 / (3 * s - t)) = 1 := by
        rw [mul_one_div, div_self (ne_of_gt h3st)]
      have hstep2 : (3 * s - t) * r ≤ (3 * s - t) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hrr (le_of_lt h3st)
      linarith [hstep1, hstep2, h3inv]
    · -- (1 - τ - 2t) * (1 - 1/r) ≥ 1 - τ - 7s
      have hr1' : 1 ≤ r := le_trans (le_max_left _ _) hrmax
      have hrc : 0 < r := lt_of_lt_of_le zero_lt_one hr1'
      have hcd : (1 - τ - 2 * t) ≤ (7 * s - 2 * t) * r := by
        have hle := mul_le_mul_of_nonneg_left hr7 (le_of_lt hd)
        have hdd : (7 * s - 2 * t) * ((1 - τ - 2 * t) / (7 * s - 2 * t)) = 1 - τ - 2 * t := by
          rw [mul_div_cancel₀ _ (ne_of_gt hd)]
        linarith [hle, hdd]
      have hcd2 : (1 - τ - 2 * t) / r ≤ 7 * s - 2 * t := by
        rw [div_le_iff₀ hrc]; exact hcd
      have hkey : (1 - τ - 2 * t) * (1 - 1 / r) = (1 - τ - 2 * t) - (1 - τ - 2 * t) / r := by
        ring
      linarith [hcd2, hkey]
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨R, hR⟩ := exists_nat_ge a
  exact ⟨R, fun r hr => ⟨h1, ha r (le_trans hR hr)⟩⟩

end Commons.Analysis.Real