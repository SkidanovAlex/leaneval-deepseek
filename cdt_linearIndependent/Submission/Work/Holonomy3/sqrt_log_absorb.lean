import Mathlib

namespace Work.Holonomy3

/-- Absorption of a multiple of `√(4mD+1)·(1+log(4mD+1))` (the proper-prime-power cost) into the
linear growth `(m·D/2)·(η/8)`, for all large `D`. -/
theorem sqrt_log_absorb {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) {B : ℝ} (hB : 0 ≤ B) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      B * (Real.sqrt (4 * (m : ℝ) * (D : ℝ) + 1) * (1 + Real.log (4 * (m : ℝ) * (D : ℝ) + 1)))
        ≤ ((m : ℝ) * (D : ℝ) / 2) * (η / 8) := by
  by_cases hB0 : B = 0
  · subst hB0
    refine ⟨0, fun D _ => ?_⟩
    simp only [zero_mul]
    exact mul_nonneg (by positivity) (by positivity)
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    -- Threshold `R` such that `D ^ (1/4) ≥ R` forces the desired inequality.
    set R : ℝ := 80 * B * (5 * (m:ℝ)) ^ (3/4:ℝ) / ((m:ℝ) * η) with hRdef
    have htend : Filter.Tendsto (fun D : ℕ => (D:ℝ) ^ (1/4:ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop R)
    refine ⟨max N 1, fun D hD => ?_⟩
    have hDN : N ≤ D := le_trans (le_max_left _ _) hD
    have hD1 : 1 ≤ D := le_trans (le_max_right _ _) hD
    have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD1
    have hD1R : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD1
    have hRle : R ≤ (D:ℝ)^(1/4:ℝ) := hN D hDN
    set t : ℝ := 4 * (m:ℝ) * (D:ℝ) + 1 with ht
    have ht1 : 1 ≤ t := by
      rw [ht]; have := mul_nonneg (le_of_lt hmpos) (le_of_lt hDpos); linarith
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    -- `log t ≤ 4 t^{1/4} ≤ ...`: sub-polynomial growth of `log`.
    have hlog : Real.log t ≤ 4 * t^(1/4:ℝ) := by
      have h := Real.log_le_rpow_div (x := t) (ε := (1/4:ℝ)) (le_of_lt htpos) (by norm_num)
      calc Real.log t ≤ t^(1/4:ℝ) / (1/4:ℝ) := h
        _ = 4 * t^(1/4:ℝ) := by rw [div_eq_mul_inv]; norm_num; ring
    have hone : (1:ℝ) ≤ t^(1/4:ℝ) := Real.one_le_rpow ht1 (by norm_num)
    have h3 : 1 + Real.log t ≤ 5 * t^(1/4:ℝ) := by linarith
    have h4 : Real.sqrt t * (1 + Real.log t) ≤ 5 * t^(3/4:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      have hrw : t^(1/2:ℝ) * t^(1/4:ℝ) = t^(3/4:ℝ) := by
        rw [← Real.rpow_add htpos]; norm_num
      calc t^(1/2:ℝ) * (1 + Real.log t)
          ≤ t^(1/2:ℝ) * (5 * t^(1/4:ℝ)) :=
            mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (le_of_lt htpos) _)
        _ = 5 * (t^(1/2:ℝ) * t^(1/4:ℝ)) := by ring
        _ = 5 * t^(3/4:ℝ) := by rw [hrw]
    have htle : t ≤ 5 * (m:ℝ) * (D:ℝ) := by
      rw [ht]; nlinarith [hm1, hD1R]
    have hstep3 : t^(3/4:ℝ) ≤ (5*(m:ℝ))^(3/4:ℝ) * (D:ℝ)^(3/4:ℝ) := by
      calc t^(3/4:ℝ) ≤ (5*(m:ℝ)*(D:ℝ))^(3/4:ℝ) :=
            Real.rpow_le_rpow (le_of_lt htpos) htle (by norm_num)
        _ = (5*(m:ℝ))^(3/4:ℝ) * (D:ℝ)^(3/4:ℝ) :=
            Real.mul_rpow (by positivity) (by positivity)
    have hfinal : 5*B*(5*(m:ℝ))^(3/4:ℝ) * (D:ℝ)^(3/4:ℝ) ≤ ((m:ℝ)*(D:ℝ)/2) * (η/8) := by
      have hRD : R * (D:ℝ)^(3/4:ℝ) ≤ (D:ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hRle (Real.rpow_nonneg (le_of_lt hDpos) (3/4))
        calc R * (D:ℝ)^(3/4:ℝ) ≤ (D:ℝ)^(1/4:ℝ) * (D:ℝ)^(3/4:ℝ) := hmul
          _ = (D:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hDpos]; norm_num
          _ = (D:ℝ) := Real.rpow_one _
      have hKR : 5*B*(5*(m:ℝ))^(3/4:ℝ) = R * ((m:ℝ)*η/16) := by
        rw [hRdef]; field_simp; ring
      rw [hKR]
      calc R * ((m:ℝ)*η/16) * (D:ℝ)^(3/4:ℝ)
          = ((m:ℝ)*η/16) * (R * (D:ℝ)^(3/4:ℝ)) := by ring
        _ ≤ ((m:ℝ)*η/16) * (D:ℝ) := mul_le_mul_of_nonneg_left hRD (by positivity)
        _ = ((m:ℝ)*(D:ℝ)/2) * (η/8) := by ring
    calc B * (Real.sqrt t * (1 + Real.log t))
        ≤ B * (5 * t^(3/4:ℝ)) := mul_le_mul_of_nonneg_left h4 (le_of_lt hBpos)
      _ = 5*B * t^(3/4:ℝ) := by ring
      _ ≤ 5*B * ((5*(m:ℝ))^(3/4:ℝ) * (D:ℝ)^(3/4:ℝ)) :=
            mul_le_mul_of_nonneg_left hstep3 (by linarith [hBpos])
      _ = 5*B*(5*(m:ℝ))^(3/4:ℝ) * (D:ℝ)^(3/4:ℝ) := by ring
      _ ≤ ((m:ℝ)*(D:ℝ)/2) * (η/8) := hfinal

end Work.Holonomy3
