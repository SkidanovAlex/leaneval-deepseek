import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Integral

open MeasureTheory

set_option autoImplicit false

theorem integral_inv_sqrt_sq_add_le {σ k T : ℝ} (hσ : 0 < σ) (hk : 0 < k) (hT : 0 < T)
    (hs : Real.sqrt σ / k ≤ T) :
    ∫ s in (0:ℝ)..T, (σ + k^2 * s^2) ^ (-(1:ℝ)/2) ≤ (1/k) * (1 + Real.log (T * k / Real.sqrt σ)) := by
  have hσpos : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  set s0 : ℝ := Real.sqrt σ / k with hs0
  have hs0pos : 0 < s0 := by rw [hs0]; exact div_pos hσpos hk
  have hs0le : s0 ≤ T := by rw [hs0]; exact hs
  set F : ℝ → ℝ := fun s => (Real.sqrt (σ + k^2 * s^2))⁻¹ with hF
  -- positivity of the base
  have hbase_pos : ∀ s : ℝ, 0 < σ + k^2 * s^2 := by
    intro s
    have : 0 ≤ k^2 * s^2 := mul_nonneg (sq_nonneg k) (sq_nonneg s)
    linarith
  have hFpos : ∀ s : ℝ, 0 < Real.sqrt (σ + k^2 * s^2) := fun s =>
    Real.sqrt_pos.mpr (hbase_pos s)
  -- rpow identity
  have hrpow : ∀ s : ℝ, (σ + k^2 * s^2) ^ (-(1:ℝ)/2) = F s := by
    intro s
    rw [hF]
    rw [show (-(1:ℝ)/2 : ℝ) = -((1:ℝ)/2) by norm_num]
    rw [Real.rpow_neg (le_of_lt (hbase_pos s))]
    rw [← Real.sqrt_eq_rpow]
  have hcont : Continuous F := by
    rw [hF]
    exact Continuous.inv₀ (Real.continuous_sqrt.comp (by continuity))
      (fun s => ne_of_gt (hFpos s))
  have hint : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    hcont.intervalIntegrable a b
  -- rewrite the integral
  have hcongr : (∫ s in (0:ℝ)..T, (σ + k^2 * s^2) ^ (-(1:ℝ)/2)) = ∫ s in (0:ℝ)..T, F s := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hrpow s
  rw [hcongr]
  -- left piece
  have hleft : (∫ s in (0:ℝ)..s0, F s) ≤ 1/k := by
    have hle1 : ∀ s ∈ Set.Icc (0:ℝ) s0, F s ≤ (Real.sqrt σ)⁻¹ := by
      intro s _
      have hle : σ ≤ σ + k^2 * s^2 := by
        have : 0 ≤ k^2 * s^2 := mul_nonneg (sq_nonneg k) (sq_nonneg s)
        linarith
      have h2 : (Real.sqrt (σ + k^2 * s^2))⁻¹ ≤ (Real.sqrt σ)⁻¹ :=
        (inv_le_inv₀ (hFpos s) hσpos).mpr (Real.sqrt_le_sqrt hle)
      rwa [hF]
    have hg : IntervalIntegrable (fun _ : ℝ => (Real.sqrt σ)⁻¹) volume (0:ℝ) s0 :=
      continuous_const.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (le_of_lt hs0pos) (hint 0 s0) hg hle1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    simp only [sub_zero] at hmono
    have hval : s0 * (Real.sqrt σ)⁻¹ = 1/k := by
      rw [hs0]; field_simp
    linarith [hmono, hval]
  -- right piece
  have hright : (∫ s in s0..T, F s) ≤ (1/k) * Real.log (T * k / Real.sqrt σ) := by
    have hle2 : ∀ s ∈ Set.Icc s0 T, F s ≤ (1/k) * s⁻¹ := by
      intro s hs'
      have hspos : 0 < s := lt_of_lt_of_le hs0pos hs'.1
      have hkspos : 0 < k * s := mul_pos hk hspos
      have hks_nonneg : 0 ≤ k * s := le_of_lt hkspos
      have hsqrt : k * s ≤ Real.sqrt (σ + k^2 * s^2) := by
        have h2 : k * s = Real.sqrt (k^2 * s^2) := by
          rw [← Real.sqrt_sq hks_nonneg]
          congr 1
          ring
        rw [h2]
        apply Real.sqrt_le_sqrt
        linarith [hσ]
      have h1 : (Real.sqrt (σ + k^2 * s^2))⁻¹ ≤ (k * s)⁻¹ :=
        (inv_le_inv₀ (hFpos s) hkspos).mpr hsqrt
      have h2 : (k * s)⁻¹ = (1/k) * s⁻¹ := by rw [one_div, mul_inv]
      rw [hF]
      exact h1.trans_eq h2
    have hGint : IntervalIntegrable (fun s : ℝ => (1/k) * s⁻¹) volume s0 T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hs0le]
      apply ContinuousOn.mul continuousOn_const
      apply continuousOn_inv₀.mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hs0pos, hx.1]
    have hmono := intervalIntegral.integral_mono_on hs0le (hint s0 T) hGint hle2
    have hGval : (∫ s in s0..T, (1/k) * s⁻¹) = (1/k) * Real.log (T * k / Real.sqrt σ) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hs0pos hT]
      congr 1
      rw [hs0]; field_simp
    linarith [hmono, hGval]
  -- split and combine
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 s0) (hint s0 T)
  rw [← hsplit]
  have hgoal_eq : (1/k) + (1/k) * Real.log (T * k / Real.sqrt σ)
      = (1/k) * (1 + Real.log (T * k / Real.sqrt σ)) := by ring
  linarith [hleft, hright, hgoal_eq]

end Commons.Analysis.Integral