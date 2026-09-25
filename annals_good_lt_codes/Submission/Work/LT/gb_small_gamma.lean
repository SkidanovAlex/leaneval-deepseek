import Mathlib

namespace Work.LT

/-- For every `c > 0` there is a small `γ > 0` with `(2e/γ)^γ ≤ 2^{c/2}`. -/
theorem gb_small_gamma (c : ℝ) (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ γ ≤ 2 ^ (c/2) - 1 ∧
      (2 * Real.exp 1 / γ) ^ γ ≤ (2:ℝ) ^ (c/2) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcL : 0 < c * Real.log 2 := mul_pos hc hL
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have htwo : 1 < (2:ℝ) ^ (c/2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hpos_diff : 0 < (2:ℝ) ^ (c/2) - 1 := by linarith
  -- Explicit small threshold on `γ`.
  set Δ : ℝ := (c * Real.log 2)^2 / (32 * Real.exp 1) with hΔdef
  have hΔpos : 0 < Δ := by
    rw [hΔdef]; apply div_pos; exact pow_pos hcL 2; positivity
  refine ⟨min (1/4) (min ((2:ℝ) ^ (c/2) - 1) Δ), ?_, ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min hpos_diff hΔpos)
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · set γ : ℝ := min (1/4) (min ((2:ℝ) ^ (c/2) - 1) Δ) with hγdef
    have hγpos : 0 < γ := by
      rw [hγdef]; exact lt_min (by norm_num) (lt_min hpos_diff hΔpos)
    have hγq : γ ≤ 1/4 := by rw [hγdef]; exact min_le_left _ _
    have hγΔ : γ ≤ Δ := by
      rw [hγdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    set B : ℝ := 2 * Real.exp 1 / γ with hBdef
    have hBpos : 0 < B := by rw [hBdef]; positivity
    -- `log B ≤ 2 √B` via `log x ≤ x^{1/2}/(1/2)`.
    have hlogB : Real.log B ≤ 2 * Real.sqrt B := by
      have h := Real.log_le_rpow_div (le_of_lt hBpos) (show (0:ℝ) < 1/2 by norm_num)
      rw [Real.sqrt_eq_rpow]
      linarith [h]
    -- `γ √B = √(2e γ)`.
    have hid : γ * Real.sqrt B = Real.sqrt (2 * Real.exp 1 * γ) := by
      calc γ * Real.sqrt B = Real.sqrt (γ^2) * Real.sqrt B := by
              rw [Real.sqrt_sq (le_of_lt hγpos)]
        _ = Real.sqrt (γ^2 * B) := by rw [Real.sqrt_mul (by positivity)]
        _ = Real.sqrt (2 * Real.exp 1 * γ) := by
              congr 1
              rw [hBdef]; field_simp
    have hsq : 2 * Real.exp 1 * γ ≤ ((c * Real.log 2)/4)^2 := by
      have h1 : 2 * Real.exp 1 * γ ≤ 2 * Real.exp 1 * Δ := by
        apply mul_le_mul_of_nonneg_left hγΔ; positivity
      rw [hΔdef] at h1
      calc 2 * Real.exp 1 * γ
            ≤ 2 * Real.exp 1 * ((c * Real.log 2)^2 / (32 * Real.exp 1)) := h1
        _ = (c * Real.log 2)^2 / 16 := by field_simp; ring
        _ = ((c * Real.log 2)/4)^2 := by ring
    have hsqrt_le : 2 * Real.sqrt (2 * Real.exp 1 * γ) ≤ (c/2) * Real.log 2 := by
      have h : Real.sqrt (2 * Real.exp 1 * γ) ≤ (c * Real.log 2)/4 := by
        calc Real.sqrt (2 * Real.exp 1 * γ) ≤ Real.sqrt (((c * Real.log 2)/4)^2) :=
                Real.sqrt_le_sqrt hsq
          _ = (c * Real.log 2)/4 := Real.sqrt_sq (by positivity)
      linarith
    have hchain : γ * Real.log B ≤ (c/2) * Real.log 2 := by
      calc γ * Real.log B ≤ γ * (2 * Real.sqrt B) :=
              mul_le_mul_of_nonneg_left hlogB (le_of_lt hγpos)
        _ = 2 * (γ * Real.sqrt B) := by ring
        _ = 2 * Real.sqrt (2 * Real.exp 1 * γ) := by rw [hid]
        _ ≤ (c/2) * Real.log 2 := hsqrt_le
    have hrpow : (2 * Real.exp 1 / γ) ^ γ = Real.exp (γ * Real.log (2 * Real.exp 1 / γ)) := by
      rw [Real.rpow_def_of_pos hBpos]; rw [hBdef]; congr 1; ring
    have hexp2 : (2:ℝ)^(c/2) = Real.exp ((c/2) * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    calc (2 * Real.exp 1 / γ)^γ = Real.exp (γ * Real.log (2 * Real.exp 1 / γ)) := hrpow
      _ ≤ Real.exp ((c/2) * Real.log 2) := Real.exp_le_exp.mpr hchain
      _ = (2:ℝ)^(c/2) := hexp2.symm

end Work.LT
