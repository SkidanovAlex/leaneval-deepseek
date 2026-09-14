import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Commons.Analysis.Integral.potential_gain_bound_stdVar_measurable

open MeasureTheory Set
open scoped Real

set_option linter.unusedVariables false

namespace Commons.Analysis.Integral

theorem intervalIntegrable_potential_gain_integrand {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : ℝ → E) (δ : E) (T c C : ℝ) (hT : 0 < T) (hc : 0 < c) (hCc : c < C)
    (hδ : δ ≠ 0) (hδT : ‖δ‖ ≤ T / 4)
    (htA : (‖δ‖ / C) ^ ((3:ℝ)/2) ≤ T / 2) (htB : (‖δ‖ / c) ^ ((3:ℝ)/2) ≤ T / 2)
    (hA : ∀ t ∈ Set.Ioc (0:ℝ) T, c * t ^ ((2:ℝ)/3) ≤ ‖A t‖ ∧ ‖A t‖ ≤ C * t ^ ((2:ℝ)/3))
    (hsign : ∀ t ∈ Set.Ioc (0:ℝ) T, 0 ≤ inner ℝ (A t) δ)
    (hAmeas : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T))) :
    IntervalIntegrable (fun t : ℝ =>
      (‖A t + (if t ≤ T - ‖δ‖ then δ else if t ≤ T then ((T - t) / ‖δ‖) • δ else 0)‖)⁻¹
        - (‖A t‖)⁻¹) MeasureTheory.volume 0 T := by
  set d : ℝ := ‖δ‖ with hd
  have hdpos : 0 < d := by rw [hd]; exact norm_pos_iff.mpr hδ
  have hdnn : 0 ≤ d := hdpos.le
  have hCpos : 0 < C := lt_trans hc hCc
  set coef : ℝ → ℝ := fun t => min 1 (max 0 ((T - t)/d)) with hcoef
  have hcoef_cont : Continuous coef := by rw [hcoef]; fun_prop
  have hcoef_nonneg : ∀ t, 0 ≤ coef t := by
    intro t; rw [hcoef]; simp only []; exact le_min (by norm_num) (le_max_left _ _)
  have hcoef_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      (if t ≤ T - d then δ else if t ≤ T then ((T - t)/d) • δ else 0) = coef t • δ := by
    intro t ht
    obtain ⟨ht0, htT1⟩ := ht
    rw [hcoef]; simp only []
    by_cases h : t ≤ T - d
    · rw [if_pos h]
      have h1 : (1:ℝ) ≤ (T - t)/d := by rw [le_div_iff₀ hdpos]; linarith
      have h0 : (0:ℝ) ≤ (T - t)/d := by linarith
      rw [max_eq_right h0, min_eq_left h1, one_smul]
    · rw [if_neg h, if_pos htT1]
      have hle1 : (T - t)/d ≤ 1 := by rw [div_le_one hdpos]; linarith
      have h0 : 0 ≤ (T-t)/d := div_nonneg (by linarith) hdpos.le
      rw [max_eq_right h0, min_eq_right hle1]
  set F : ℝ → ℝ := fun t => (‖A t + coef t • δ‖)⁻¹ - (‖A t‖)⁻¹ with hF
  have hAt_pos : ∀ t ∈ Set.Ioc (0:ℝ) T, 0 < ‖A t‖ := by
    intro t ht
    obtain ⟨hlow, _⟩ := hA t ht
    have : 0 < c * t ^ ((2:ℝ)/3) := mul_pos hc (Real.rpow_pos_of_pos ht.1 _)
    linarith
  have hnorm_ge : ∀ t ∈ Set.Ioc (0:ℝ) T, ‖A t‖ ≤ ‖A t + coef t • δ‖ := by
    intro t ht
    have hs := hsign t ht
    have hnn := hcoef_nonneg t
    have h2 : (‖A t‖)^2 ≤ ‖A t + coef t • δ‖^2 := by
      rw [norm_add_sq_real]
      rw [real_inner_smul_right]
      nlinarith [mul_nonneg hnn hs, sq_nonneg ‖coef t • δ‖]
    nlinarith [h2, norm_nonneg (A t), norm_nonneg (A t + coef t • δ)]
  -- integrability of the majorant `1/(c t^{2/3})`
  have hKint : IntervalIntegrable (fun t : ℝ => 1/(c * t ^ ((2:ℝ)/3))) volume (0:ℝ) T := by
    have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(2:ℝ)/3)) volume (0:ℝ) T :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(2:ℝ)/3)
    refine IntervalIntegrable.congr ?_ (hbase.const_mul c⁻¹)
    intro t ht
    rw [Set.uIoc_of_le hT.le, Set.mem_Ioc] at ht
    simp only []
    rw [show (-(2:ℝ))/3 = -((2:ℝ)/3) by ring, Real.rpow_neg ht.1.le (2/3), one_div, mul_inv]
  have hF_meas : AEStronglyMeasurable F (volume.restrict (Set.Ioc (0:ℝ) T)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => A t + coef t • δ)
        (volume.restrict (Set.Ioc (0:ℝ) T)) := by
      refine hAmeas.add ?_
      exact (Continuous.aestronglyMeasurable
        (μ := volume.restrict (Set.Ioc (0:ℝ) T)) hcoef_cont).smul_const δ
    simp only [hF]
    exact ((h1.norm).aemeasurable.inv).aestronglyMeasurable.sub
      (((hAmeas.norm).aemeasurable.inv).aestronglyMeasurable)
  have hF_int : IntervalIntegrable F volume (0:ℝ) T := by
    refine hKint.mono_fun' ?_ ?_
    · rw [Set.uIoc_of_le hT.le]; exact hF_meas
    · rw [Set.uIoc_of_le hT.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have h1 := hnorm_ge t ht
      have h2 := hAt_pos t ht
      have h3 := inv_anti₀ h2 h1
      have h4 : (‖A t‖)⁻¹ ≤ 1/(c * t^((2:ℝ)/3)) := by
        rw [one_div]
        exact inv_anti₀ (mul_pos hc (Real.rpow_pos_of_pos ht.1 _)) (hA t ht).1
      have h5 : 0 ≤ (‖A t + coef t • δ‖)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      simp only [hF]
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub]
      linarith
  -- transfer from `coef`-version `F` to the statement's piecewise expression
  have hEqOn : EqOn F (fun t : ℝ =>
      (‖A t + (if t ≤ T - ‖δ‖ then δ else if t ≤ T then ((T - t) / ‖δ‖) • δ else 0)‖)⁻¹
        - (‖A t‖)⁻¹) (Set.uIoc (0:ℝ) T) := by
    intro t ht
    rw [Set.uIoc_of_le hT.le] at ht
    have htIcc : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1.le, ht.2⟩
    simp only [hF]
    have hkey : (if t ≤ T - ‖δ‖ then δ else if t ≤ T then ((T - t)/‖δ‖) • δ else 0)
        = coef t • δ := by
      rw [← hd]
      exact hcoef_eq t htIcc
    rw [hkey]
  exact IntervalIntegrable.congr hEqOn hF_int

end Commons.Analysis.Integral