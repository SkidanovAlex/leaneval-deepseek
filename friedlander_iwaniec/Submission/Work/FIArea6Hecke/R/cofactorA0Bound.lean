import Mathlib

namespace Work.FIArea6Hecke.R

theorem cofactorA0Bound (C K c D : ℝ) (hC : 0 < C) (hK : 0 ≤ K) (hc : 0 ≤ c) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ T : ℝ, 1 ≤ T →
      c * T * (Real.log (T + 2) + K + 1) * (Real.log T + D)
        ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 + A₀ := by
  set m : ℝ := max 1 ((D - 4 * K - 4) / 3) with hm
  set T₁ : ℝ := Real.exp m + 3 with hT₁
  set M : ℝ := Real.log (T₁ + 2) + K + 1 with hM
  set P : ℝ := max (Real.log T₁ + D) 0 with hP
  set A₀ : ℝ := c * T₁ * M * P with hA₀
  have hm_ge : (D - 4 * K - 4) / 3 ≤ m := by rw [hm]; exact le_max_right _ _
  have hT1_pos : 0 < T₁ := by rw [hT₁]; linarith [Real.exp_pos m]
  have hexp_le : Real.exp m ≤ T₁ + 2 := by rw [hT₁]; linarith [Real.exp_pos m]
  have hlogm : m ≤ Real.log (T₁ + 2) := by
    rw [← Real.log_exp m]
    exact Real.log_le_log (Real.exp_pos m) hexp_le
  have hM_nonneg : 0 ≤ M := by
    rw [hM]
    have : 0 < Real.log (T₁ + 2) := Real.log_pos (by linarith)
    linarith
  have hP_nonneg : 0 ≤ P := by rw [hP]; exact le_max_right _ _
  have hA₀_nonneg : 0 ≤ A₀ := by
    rw [hA₀]
    exact mul_nonneg (mul_nonneg (mul_nonneg hc hT1_pos.le) hM_nonneg) hP_nonneg
  refine ⟨A₀, hA₀_nonneg, ?_⟩
  intro T hT
  have hT_pos : 0 < T := by linarith
  have hlogT2_pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hL_nonneg : 0 ≤ Real.log (T + 2) + K + 1 := by linarith
  have hfac : 0 ≤ c * T * (Real.log (T + 2) + K + 1) :=
    mul_nonneg (mul_nonneg hc hT_pos.le) hL_nonneg
  rcases le_total T T₁ with hle | hge
  · -- Case T ≤ T₁
    have hlogT_le : Real.log T ≤ Real.log T₁ := Real.log_le_log hT_pos hle
    have hlogD_le_P : Real.log T + D ≤ P := by
      rw [hP]
      calc Real.log T + D ≤ Real.log T₁ + D := by linarith
        _ ≤ max (Real.log T₁ + D) 0 := le_max_left _ _
    have hL_le_M : Real.log (T + 2) + K + 1 ≤ M := by
      rw [hM]
      have h2 : Real.log (T + 2) ≤ Real.log (T₁ + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hstep1 : c * T * (Real.log (T + 2) + K + 1) * (Real.log T + D)
        ≤ c * T * (Real.log (T + 2) + K + 1) * P :=
      mul_le_mul_of_nonneg_left hlogD_le_P hfac
    have hcT : c * T ≤ c * T₁ := mul_le_mul_of_nonneg_left hle hc
    have hLP : (Real.log (T + 2) + K + 1) * P ≤ M * P :=
      mul_le_mul_of_nonneg_right hL_le_M hP_nonneg
    have hstep2 : c * T * (Real.log (T + 2) + K + 1) * P ≤ c * T₁ * M * P := by
      have h : (c * T) * ((Real.log (T + 2) + K + 1) * P) ≤ (c * T₁) * (M * P) :=
        mul_le_mul hcT hLP (mul_nonneg hL_nonneg hP_nonneg) (mul_nonneg hc hT1_pos.le)
      nlinarith [h]
    have hRHS_nonneg : 0 ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) hT_pos.le)
        (sq_nonneg (Real.log (T + 2) + K + 1))
    rw [hA₀]
    linarith [hstep1, hstep2, hRHS_nonneg]
  · -- Case T₁ ≤ T
    have hlogT_le_T2 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hT_pos (by linarith)
    have hlog_mono : Real.log (T₁ + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hm_le : m ≤ Real.log (T + 2) := le_trans hlogm hlog_mono
    have hD_le : D ≤ 3 * Real.log (T + 2) + 4 * K + 4 := by linarith [hm_ge, hm_le]
    have hlogD : Real.log T + D ≤ 4 * (Real.log (T + 2) + K + 1) := by linarith
    have hstep1 : c * T * (Real.log (T + 2) + K + 1) * (Real.log T + D)
        ≤ c * T * (Real.log (T + 2) + K + 1)
            * (4 * (Real.log (T + 2) + K + 1)) :=
      mul_le_mul_of_nonneg_left hlogD hfac
    have hEq : c * T * (Real.log (T + 2) + K + 1) * (4 * (Real.log (T + 2) + K + 1))
        = 4 * c * T * (Real.log (T + 2) + K + 1) ^ 2 := by ring
    have hstep3 : 4 * c * T * (Real.log (T + 2) + K + 1) ^ 2
        ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hC.le hT_pos.le)
        (sq_nonneg (Real.log (T + 2) + K + 1))]
    linarith [hstep1, hEq, hstep3, hA₀_nonneg]

end Work.FIArea6Hecke.R
