import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Work.BMF

/-- The function `t ↦ (√(σ² + t²))⁻¹` is continuous for `σ > 0`. -/
private lemma continuous_sqrt_inv {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun t : ℝ => (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹) := by
  apply Continuous.inv₀
  · exact Real.continuous_sqrt.comp (by continuity)
  · intro t
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

/-- Bound for the integral over `[0,T]`. -/
private lemma half_bound {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    (∫ t in (0)..T, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹) ≤ 1 + Real.log (2 + T / σ) := by
  have hcont : Continuous (fun t : ℝ => (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹) :=
    continuous_sqrt_inv hσ
  rcases lt_or_ge σ T with hσT | hTσ
  · have hsplit : (∫ t in (0)..T, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹)
        = (∫ t in (0)..σ, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹)
          + (∫ t in σ..T, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹) := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) 0 σ)
        (hcont.intervalIntegrable (μ := volume) σ T)).symm
    have h1 : (∫ t in (0)..σ, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹) ≤ 1 := by
      have hle : ∀ t ∈ Set.Icc (0:ℝ) σ, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹ ≤ σ⁻¹ := by
        intro t ht
        rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) hσ]
        rw [Real.le_sqrt (le_of_lt hσ) (by positivity)]
        nlinarith [sq_nonneg t]
      have hI := intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hσ)
        (hcont.intervalIntegrable (μ := volume) 0 σ) intervalIntegrable_const hle
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hI
      have : σ * σ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hσ)
      linarith
    have h2 : (∫ t in σ..T, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹) ≤ Real.log (T / σ) := by
      have hle : ∀ t ∈ Set.Icc σ T, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹ ≤ t⁻¹ := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hσ ht.1
        rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) ht0]
        rw [Real.le_sqrt (le_of_lt ht0) (by positivity)]
        nlinarith [sq_nonneg σ]
      have hint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume σ T := by
        have h := intervalIntegral.intervalIntegrable_inv (μ := volume) (f := fun x : ℝ => x) (a := σ) (b := T)
          (fun x hx => by
            rw [Set.uIcc_of_le (le_of_lt hσT)] at hx
            exact ne_of_gt (lt_of_lt_of_le hσ hx.1)) continuousOn_id
        simpa using h
      have hI := intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hσT)
        (hcont.intervalIntegrable (μ := volume) σ T) hint hle
      have hzero : (0:ℝ) ∉ Set.uIcc σ T := by
        rw [Set.uIcc_of_le (le_of_lt hσT)]
        intro hx
        exact absurd hx.1 (not_le.mpr hσ)
      rw [integral_inv hzero] at hI
      exact hI
    rw [hsplit]
    have hlog : Real.log (T / σ) ≤ Real.log (2 + T / σ) := by
      apply Real.log_le_log (div_pos hT hσ)
      linarith
    linarith
  · have hle : ∀ t ∈ Set.Icc (0:ℝ) T, (Real.sqrt (σ ^ 2 + t ^ 2))⁻¹ ≤ σ⁻¹ := by
      intro t ht
      rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) hσ]
      rw [Real.le_sqrt (le_of_lt hσ) (by positivity)]
      nlinarith [sq_nonneg t]
    have hI := intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hT)
      (hcont.intervalIntegrable (μ := volume) 0 T) intervalIntegrable_const hle
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hI
    have hT1 : T * σ⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hσ).mpr hTσ
    have hlog : (0:ℝ) ≤ Real.log (2 + T / σ) := by
      apply Real.log_nonneg
      have : 0 < T / σ := div_pos hT hσ
      linarith
    linarith

theorem integral_inv_sqrt_sq_add_sq_le {σ₁ T : ℝ} (hσ : 0 < σ₁) (hT : 0 < T) :
    (∫ t in (-T)..T, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹) ≤ 2 + 2 * Real.log (2 + T / σ₁) := by
  have hcont : Continuous (fun t : ℝ => (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹) :=
    continuous_sqrt_inv hσ
  -- symmetry: the integral over `[-T, 0]` equals the one over `[0, T]`
  have hsym : (∫ t in (-T)..0, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹)
      = ∫ t in (0)..T, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹ := by
    have h1 := intervalIntegral.integral_comp_neg (a := -T) (b := 0)
      (fun t : ℝ => (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹)
    simp only [neg_zero, neg_neg] at h1
    have h2 : (∫ t in (-T)..0, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹)
        = ∫ t in (-T)..0, (Real.sqrt (σ₁ ^ 2 + (-t) ^ 2))⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [neg_sq]
    rw [h2, h1]
  have hadd : (∫ t in (-T)..T, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹)
      = (∫ t in (-T)..0, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹)
        + ∫ t in (0)..T, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹ := by
    exact (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable (μ := volume) (-T) 0)
      (hcont.intervalIntegrable (μ := volume) 0 T)).symm
  rw [hadd, hsym]
  have hhalf := half_bound hσ hT
  linarith

end Work.BMF
