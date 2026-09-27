import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

theorem step10_upper {ρ κ r : ℝ} {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) (hκκ : kappa G = κ)
    (hr : |r| * κ ≤ (ρ⁻¹) ^ 5) :
    drift G r ≤ 2 * (ρ⁻¹) ^ 10 ∧ |G 1 0 * r| ≤ (ρ⁻¹) ^ 5 * κ := by
  have hκnn : 0 ≤ κ := le_of_lt hκ
  -- powers of ρ⁻¹
  have hρinv_pos : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hρinv_ge1 : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ0).mpr hρ1
  have h5 : (1 : ℝ) ≤ (ρ⁻¹) ^ 5 := one_le_pow₀ hρinv_ge1
  have h510 : (ρ⁻¹) ^ 5 ≤ (ρ⁻¹) ^ 10 := pow_le_pow_right₀ hρinv_ge1 (by norm_num)
  have h5le : (ρ⁻¹) ^ 5 ≤ 2 * (ρ⁻¹) ^ 10 := by linarith
  -- component bounds coming from kappa G = κ
  have hka : |G 1 1 - G 0 0| ≤ κ :=
    le_trans (le_max_left (kappaA G) (kappaU G)) (le_of_eq hκκ)
  have hU : kappaU G ≤ κ := by rw [← hκκ]; exact le_max_right _ _
  have hsqrt : Real.sqrt |G 1 0| ≤ κ := le_trans (le_max_left _ _) hU
  have h12 : |G 1 2| ≤ κ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hU)
  have h20 : |G 2 0| ≤ κ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hU)
  have h10 : |G 1 0| ≤ κ ^ 2 := (Real.sqrt_le_left hκnn).mp hsqrt
  -- r bound
  have hkr : κ * |r| ≤ (ρ⁻¹) ^ 5 := by rw [mul_comm]; exact hr
  -- individual product bounds
  have hA1 : |(G 1 1 - G 0 0) * r| ≤ (ρ⁻¹) ^ 5 :=
    calc |(G 1 1 - G 0 0) * r| = |G 1 1 - G 0 0| * |r| := by rw [abs_mul]
      _ ≤ κ * |r| := mul_le_mul_of_nonneg_right hka (abs_nonneg r)
      _ ≤ (ρ⁻¹) ^ 5 := hkr
  have hA2 : |G 1 0 * r ^ 2| ≤ (ρ⁻¹) ^ 10 := by
    rw [abs_mul, abs_pow]
    have h1 : |G 1 0| * |r| ^ 2 ≤ κ ^ 2 * |r| ^ 2 :=
      mul_le_mul_of_nonneg_right h10 (by positivity)
    have h2 : κ ^ 2 * |r| ^ 2 = (κ * |r|) ^ 2 := by ring
    have h3 : (κ * |r|) ^ 2 ≤ ((ρ⁻¹) ^ 5) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hkr 2
    have h4 : ((ρ⁻¹) ^ 5) ^ 2 = (ρ⁻¹) ^ 10 := by rw [← pow_mul]
    linarith
  have hD : |G 1 2 * r| ≤ (ρ⁻¹) ^ 5 :=
    calc |G 1 2 * r| = |G 1 2| * |r| := by rw [abs_mul]
      _ ≤ κ * |r| := mul_le_mul_of_nonneg_right h12 (abs_nonneg r)
      _ ≤ (ρ⁻¹) ^ 5 := hkr
  have hC : |G 2 0 * r| ≤ (ρ⁻¹) ^ 5 :=
    calc |G 2 0 * r| = |G 2 0| * |r| := by rw [abs_mul]
      _ ≤ κ * |r| := mul_le_mul_of_nonneg_right h20 (abs_nonneg r)
      _ ≤ (ρ⁻¹) ^ 5 := hkr
  have hT1 : |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| ≤ (ρ⁻¹) ^ 5 + (ρ⁻¹) ^ 10 :=
    calc |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2|
        ≤ |(G 1 1 - G 0 0) * r| + |G 1 0 * r ^ 2| := abs_sub _ _
      _ ≤ (ρ⁻¹) ^ 5 + (ρ⁻¹) ^ 10 := add_le_add hA1 hA2
  have hA'' : |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| ≤ 2 * (ρ⁻¹) ^ 10 := by
    linarith [hT1, h510]
  have hB'' : |G 1 2 * r| ≤ 2 * (ρ⁻¹) ^ 10 := by linarith [hD, h5le]
  have hC'' : |G 2 0 * r| ≤ 2 * (ρ⁻¹) ^ 10 := by linarith [hC, h5le]
  constructor
  · rw [drift]; exact max_le (max_le hA'' hB'') hC''
  · rw [abs_mul]
    calc |G 1 0| * |r| ≤ κ ^ 2 * |r| := mul_le_mul_of_nonneg_right h10 (abs_nonneg r)
      _ = κ * (κ * |r|) := by ring
      _ ≤ κ * (ρ⁻¹) ^ 5 := mul_le_mul_of_nonneg_left hkr hκnn
      _ = (ρ⁻¹) ^ 5 * κ := by ring

end Work.EKLC8Core
