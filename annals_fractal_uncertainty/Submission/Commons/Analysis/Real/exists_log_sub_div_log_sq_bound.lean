import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- For `x ≥ 0`, `log x ≤ 4 * x ^ (1/4)`. -/
private theorem log_le_four_rpow_quarter {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
  have hε : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  calc Real.log x ≤ x ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) := Real.log_le_rpow_div hx hε
    _ = 4 * x ^ ((1 : ℝ) / 4) := by ring

/-- For `t ≥ 2`, `log (1 + t) ≤ (4 * 2^(1/4)) * t^(1/4)`. -/
private theorem log_one_add_le_quarter {t : ℝ} (ht : 2 ≤ t) :
    Real.log (1 + t) ≤ (4 * (2 : ℝ) ^ ((1 : ℝ) / 4)) * t ^ ((1 : ℝ) / 4) := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : 0 ≤ 1 + t := by linarith
  have h2 : 0 ≤ 2 * t := by positivity
  have hle : 1 + t ≤ 2 * t := by linarith
  have hε : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  calc Real.log (1 + t) ≤ 4 * (1 + t) ^ ((1 : ℝ) / 4) := log_le_four_rpow_quarter h1
    _ ≤ 4 * (2 * t) ^ ((1 : ℝ) / 4) := by
        have hr := (Real.rpow_le_rpow_iff h1 h2 hε).2 hle
        linarith
    _ = (4 * (2 : ℝ) ^ ((1 : ℝ) / 4)) * t ^ ((1 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0]
        ring

/-- For `t ≥ 2`, `log (2 + t) ≤ (4 * 2^(1/4)) * t^(1/4)`. -/
private theorem log_two_add_le_quarter {t : ℝ} (ht : 2 ≤ t) :
    Real.log (2 + t) ≤ (4 * (2 : ℝ) ^ ((1 : ℝ) / 4)) * t ^ ((1 : ℝ) / 4) := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : 0 ≤ 2 + t := by linarith
  have h2 : 0 ≤ 2 * t := by positivity
  have hle : 2 + t ≤ 2 * t := by linarith
  have hε : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  calc Real.log (2 + t) ≤ 4 * (2 + t) ^ ((1 : ℝ) / 4) := log_le_four_rpow_quarter h1
    _ ≤ 4 * (2 * t) ^ ((1 : ℝ) / 4) := by
        have hr := (Real.rpow_le_rpow_iff h1 h2 hε).2 hle
        linarith
    _ = (4 * (2 : ℝ) ^ ((1 : ℝ) / 4)) * t ^ ((1 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0]
        ring

theorem exists_log_sub_div_log_sq_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      a * Real.log (1 + t) - b * (t / (Real.log (2 + t)) ^ 2) ≤ B := by
  set K : ℝ := 4 * (2 : ℝ) ^ ((1 : ℝ) / 4) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h2 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  set c : ℝ := a * K ^ 3 / b with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos (by positivity) hb
  have hc_nonneg : 0 ≤ c := hcpos.le
  set T : ℝ := max 2 (c ^ 4) with hT
  have hT2 : 2 ≤ T := le_max_left _ _
  have hc4T : c ^ 4 ≤ T := le_max_right _ _
  refine ⟨a * T, ?_⟩
  intro t ht
  by_cases hle : t ≤ T
  · -- Bounded region: the negative term is nonpositive, `log (1+t) ≤ t`.
    have hnonneg : 0 ≤ b * (t / (Real.log (2 + t)) ^ 2) := by
      apply mul_nonneg hb.le
      exact div_nonneg ht (sq_nonneg _)
    have hlogle : Real.log (1 + t) ≤ t := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + t)
      linarith
    have h1 : a * Real.log (1 + t) ≤ a * t := mul_le_mul_of_nonneg_left hlogle ha.le
    have h2 : a * t ≤ a * T := mul_le_mul_of_nonneg_left hle ha.le
    linarith
  · -- Large region: the positive `t/log^2` term dominates.
    rw [not_le] at hle
    have hTt : max 2 (c ^ 4) ≤ t := le_of_lt hle
    have ht2 : 2 ≤ t := le_trans (le_max_left _ _) hTt
    have hc4t : c ^ 4 ≤ t := le_trans (le_max_right _ _) hTt
    have htpos : 0 < t := by linarith
    have ht0 : 0 ≤ t := ht
    have hlog1 : Real.log (1 + t) ≤ K * t ^ ((1 : ℝ) / 4) := by
      have h := log_one_add_le_quarter ht2
      rwa [← hK] at h
    have hlog2 : Real.log (2 + t) ≤ K * t ^ ((1 : ℝ) / 4) := by
      have h := log_two_add_le_quarter ht2
      rwa [← hK] at h
    have hlog2_nonneg : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
    have htq_nonneg : 0 ≤ t ^ ((1 : ℝ) / 4) := Real.rpow_nonneg ht0 _
    -- Bound the square of the second logarithm.
    have hsq : (Real.log (2 + t)) ^ 2 ≤ K ^ 2 * t ^ ((1 : ℝ) / 2) := by
      have hsq1 : (Real.log (2 + t)) ^ 2 ≤ (K * t ^ ((1 : ℝ) / 4)) ^ 2 :=
        pow_le_pow_left₀ hlog2_nonneg hlog2 2
      have hexp : (K * t ^ ((1 : ℝ) / 4)) ^ 2 = K ^ 2 * t ^ ((1 : ℝ) / 2) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_mul_natCast ht0 ((1 : ℝ) / 4) 2]
        norm_num
      rwa [hexp] at hsq1
    -- Multiply the two logarithm bounds.
    have hprod : a * Real.log (1 + t) * (Real.log (2 + t)) ^ 2
        ≤ a * K ^ 3 * t ^ ((3 : ℝ) / 4) := by
      have h1 : a * Real.log (1 + t) ≤ a * K * t ^ ((1 : ℝ) / 4) := by
        have := mul_le_mul_of_nonneg_left hlog1 ha.le
        nlinarith [this]
      have h3 : (a * Real.log (1 + t)) * (Real.log (2 + t)) ^ 2
          ≤ (a * K * t ^ ((1 : ℝ) / 4)) * (K ^ 2 * t ^ ((1 : ℝ) / 2)) :=
        mul_le_mul h1 hsq (sq_nonneg _) (mul_nonneg (mul_nonneg ha.le hKpos.le) htq_nonneg)
      have huv : t ^ ((1 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) = t ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add htpos ((1 : ℝ) / 4) ((1 : ℝ) / 2)]
        norm_num
      have hRHS : (a * K * t ^ ((1 : ℝ) / 4)) * (K ^ 2 * t ^ ((1 : ℝ) / 2))
          = a * K ^ 3 * t ^ ((3 : ℝ) / 4) := by
        rw [show (a * K * t ^ ((1 : ℝ) / 4)) * (K ^ 2 * t ^ ((1 : ℝ) / 2))
              = a * K ^ 3 * (t ^ ((1 : ℝ) / 4) * t ^ ((1 : ℝ) / 2)) by ring]
        rw [huv]
      calc a * Real.log (1 + t) * (Real.log (2 + t)) ^ 2
          = (a * Real.log (1 + t)) * (Real.log (2 + t)) ^ 2 := by ring
        _ ≤ (a * K * t ^ ((1 : ℝ) / 4)) * (K ^ 2 * t ^ ((1 : ℝ) / 2)) := h3
        _ = a * K ^ 3 * t ^ ((3 : ℝ) / 4) := hRHS
    -- Extract `t^(1/4) ≥ c`.
    have hroot : c ≤ t ^ ((1 : ℝ) / 4) := by
      have hcroot : (c ^ 4) ^ ((1 : ℝ) / 4) = c := by
        have h := Real.pow_rpow_inv_natCast hc_nonneg (n := 4) (by norm_num : (4 : ℕ) ≠ 0)
        simpa [one_div] using h
      have hchain : (c ^ 4) ^ ((1 : ℝ) / 4) ≤ t ^ ((1 : ℝ) / 4) :=
        (Real.rpow_le_rpow_iff (pow_nonneg hc_nonneg 4) ht0 (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).2 hc4t
      rwa [hcroot] at hchain
    have hbt14 : a * K ^ 3 ≤ b * t ^ ((1 : ℝ) / 4) := by
      have hbc : b * c = a * K ^ 3 := by
        rw [hc]; field_simp
      have := mul_le_mul_of_nonneg_left hroot hb.le
      linarith [this, hbc]
    have ht34_nonneg : 0 ≤ t ^ ((3 : ℝ) / 4) := Real.rpow_nonneg ht0 _
    have hbt : a * K ^ 3 * t ^ ((3 : ℝ) / 4) ≤ b * t := by
      have hmul := mul_le_mul_of_nonneg_right hbt14 ht34_nonneg
      have hpow : t ^ ((1 : ℝ) / 4) * t ^ ((3 : ℝ) / 4) = t := by
        rw [← Real.rpow_add htpos ((1 : ℝ) / 4) ((3 : ℝ) / 4)]
        norm_num
      calc a * K ^ 3 * t ^ ((3 : ℝ) / 4) = (a * K ^ 3) * t ^ ((3 : ℝ) / 4) := by ring
        _ ≤ (b * t ^ ((1 : ℝ) / 4)) * t ^ ((3 : ℝ) / 4) := hmul
        _ = b * (t ^ ((1 : ℝ) / 4) * t ^ ((3 : ℝ) / 4)) := by ring
        _ = b * t := by rw [hpow]
    have hfin : a * Real.log (1 + t) ≤ b * (t / (Real.log (2 + t)) ^ 2) := by
      have hlog2pos : 0 < Real.log (2 + t) := Real.log_pos (by linarith)
      have hsqpos : 0 < (Real.log (2 + t)) ^ 2 := pow_pos hlog2pos 2
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hsqpos]
      exact le_trans hprod hbt
    have : a * Real.log (1 + t) - b * (t / (Real.log (2 + t)) ^ 2) ≤ 0 := by linarith
    have hBT : 0 ≤ a * T := mul_nonneg ha.le (by linarith [hT2])
    linarith

end Commons.Analysis.Real