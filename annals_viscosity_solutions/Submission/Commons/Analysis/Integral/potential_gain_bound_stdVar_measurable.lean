import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Integral.rpow_neg_two_thirds_integral

open MeasureTheory Set
open scoped Real

namespace Commons.Analysis.Integral

theorem potential_gain_bound_stdVar_measurable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : ℝ → E) (δ : E) (T c C : ℝ) (hT : 0 < T) (hc : 0 < c) (hCc : c < C)
    (hδ : δ ≠ 0) (hδT : ‖δ‖ ≤ T / 4)
    (htA : (‖δ‖ / C) ^ ((3:ℝ)/2) ≤ T / 2) (htB : (‖δ‖ / c) ^ ((3:ℝ)/2) ≤ T / 2)
    (hA : ∀ t ∈ Set.Ioc (0:ℝ) T, c * t ^ ((2:ℝ)/3) ≤ ‖A t‖ ∧ ‖A t‖ ≤ C * t ^ ((2:ℝ)/3))
    (hsign : ∀ t ∈ Set.Ioc (0:ℝ) T, 0 ≤ inner ℝ (A t) δ)
    (hAmeas : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T))) :
    ∫ t in (0:ℝ)..T,
      ((‖A t + (if t ≤ T - ‖δ‖ then δ else if t ≤ T then ((T - t) / ‖δ‖) • δ else 0)‖)⁻¹
        - (‖A t‖)⁻¹)
      ≤ -‖δ‖ ^ ((1:ℝ)/2) * (1 - c ^ 2 / C ^ 2) / (2 * C ^ ((3:ℝ)/2))
        + 2 * ‖δ‖ / (c * (T / 2) ^ ((2:ℝ)/3)):= by
  set d : ℝ := ‖δ‖ with hd
  have hdpos : 0 < d := by rw [hd]; exact norm_pos_iff.mpr hδ
  have hdnn : 0 ≤ d := hdpos.le
  have hCpos : 0 < C := lt_trans hc hCc
  set t₁ : ℝ := (d / C) ^ ((3:ℝ)/2) with ht₁
  have ht₁pos : 0 < t₁ := by rw [ht₁]; positivity
  have ht₁T : t₁ ≤ T := by linarith
  have ht₁Td : t₁ ≤ T - d := by linarith
  set coef : ℝ → ℝ := fun t => min 1 (max 0 ((T - t)/d)) with hcoef
  have hcoef_cont : Continuous coef := by rw [hcoef]; fun_prop
  have hcoef_nonneg : ∀ t, 0 ≤ coef t := by
    intro t; rw [hcoef]; simp only []; exact le_min (by norm_num) (le_max_left _ _)
  have hcoef_le_one : ∀ t, coef t ≤ 1 := by
    intro t; rw [hcoef]; simp only []; exact min_le_left _ _
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
  have hcongr : EqOn
      (fun t => (‖A t + (if t ≤ T - d then δ else if t ≤ T then ((T - t) / d) • δ else 0)‖)⁻¹ - (‖A t‖)⁻¹)
      (fun t => (‖A t + coef t • δ‖)⁻¹ - (‖A t‖)⁻¹) (Set.uIcc (0:ℝ) T) := by
    intro t ht
    rw [Set.uIcc_of_le hT.le] at ht
    simp only []
    rw [hcoef_eq t ht]
  rw [intervalIntegral.integral_congr hcongr]
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
  have hF_le_zero : ∀ t ∈ Set.Ioc (0:ℝ) T, F t ≤ 0 := by
    intro t ht
    have h1 := hnorm_ge t ht
    have h2 := hAt_pos t ht
    have h3 := inv_anti₀ h2 h1
    simp only [hF]
    linarith
  have hcoef_one : ∀ t ∈ Set.Ioo (0:ℝ) t₁, coef t = 1 := by
    intro t ht
    obtain ⟨ht0, htt⟩ := ht
    rw [hcoef]; simp only []
    have hle : t ≤ T - d := le_trans htt.le ht₁Td
    have h1 : (1:ℝ) ≤ (T - t)/d := by rw [le_div_iff₀ hdpos]; linarith
    have h0 : (0:ℝ) ≤ (T - t)/d := by linarith
    rw [max_eq_right h0, min_eq_left h1]
  have hF_le_g : ∀ t ∈ Set.Ioo (0:ℝ) t₁, F t ≤ 1/d - 1/(C * t ^ ((2:ℝ)/3)) := by
    intro t ht
    obtain ⟨ht0, htt⟩ := ht
    have htT : t ∈ Set.Ioc (0:ℝ) T := ⟨ht0, le_trans htt.le ht₁T⟩
    have hc1 := hcoef_one t ⟨ht0, htt⟩
    obtain ⟨hlow, hhigh⟩ := hA t htT
    have hdlt : d ≤ ‖A t + δ‖ := by
      have hsq : d^2 ≤ ‖A t + δ‖^2 := by
        rw [norm_add_sq_real]
        have hs := hsign t htT
        have hδ2 : ‖δ‖^2 = d^2 := by rw [hd]
        nlinarith
      nlinarith [hsq, hdnn, norm_nonneg (A t + δ)]
    simp only [hF]
    rw [hc1, one_smul]
    have h_inv1 : (‖A t + δ‖)⁻¹ ≤ 1/d := by
      rw [one_div]; exact inv_anti₀ hdpos hdlt
    have h_inv2 : 1/(C * t ^ ((2:ℝ)/3)) ≤ (‖A t‖)⁻¹ := by
      have hpos : 0 < ‖A t‖ := by
        have : 0 < c * t^((2:ℝ)/3) := mul_pos hc (Real.rpow_pos_of_pos ht0 _)
        linarith
      rw [one_div]; exact inv_anti₀ hpos hhigh
    linarith
  -- integrability of the majorant
  have hKint : ∀ (K b : ℝ), 0 < K → 0 ≤ b →
      IntervalIntegrable (fun t : ℝ => 1/(K * t ^ ((2:ℝ)/3))) volume (0:ℝ) b := by
    intro K b hK hb
    have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(2:ℝ)/3)) volume (0:ℝ) b :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(2:ℝ)/3)
    refine IntervalIntegrable.congr ?_ (hbase.const_mul K⁻¹)
    intro t ht
    rw [Set.uIoc_of_le hb, Set.mem_Ioc] at ht
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
    refine (hKint c T hc hT.le).mono_fun' ?_ ?_
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
  have hsub1 : Set.uIcc (0:ℝ) t₁ ⊆ Set.uIcc (0:ℝ) T := by
    rw [Set.uIcc_of_le ht₁pos.le, Set.uIcc_of_le hT.le]
    exact Set.Icc_subset_Icc le_rfl ht₁T
  have hsub2 : Set.uIcc t₁ T ⊆ Set.uIcc (0:ℝ) T := by
    rw [Set.uIcc_of_le ht₁T, Set.uIcc_of_le hT.le]
    exact Set.Icc_subset_Icc ht₁pos.le le_rfl
  have hF_int1 : IntervalIntegrable F volume (0:ℝ) t₁ := hF_int.mono_set hsub1
  have hF_int2 : IntervalIntegrable F volume t₁ T := hF_int.mono_set hsub2
  have hg_int : IntervalIntegrable (fun t : ℝ => 1/d - 1/(C * t ^ ((2:ℝ)/3))) volume (0:ℝ) t₁ :=
    intervalIntegrable_const.sub (hKint C t₁ hCpos ht₁pos.le)
  have hstep1 : ∫ t in (0:ℝ)..t₁, F t ≤
      ∫ t in (0:ℝ)..t₁, (1/d - 1/(C * t ^ ((2:ℝ)/3))) :=
    intervalIntegral.integral_mono_on_of_le_Ioo ht₁pos.le hF_int1 hg_int (fun t ht => hF_le_g t ht)
  have hstep2 : ∫ t in t₁..T, F t ≤ 0 := by
    rw [← neg_nonneg, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_nonneg ht₁T (fun u hu => ?_)
    rw [neg_nonneg]
    exact hF_le_zero u ⟨lt_of_lt_of_le ht₁pos hu.1, hu.2⟩
  have hg_val : ∫ t in (0:ℝ)..t₁, (1/d - 1/(C * t ^ ((2:ℝ)/3))) =
      -2 * d^((1:ℝ)/2)/C^((3:ℝ)/2) := by
    have hI1 : ∫ t in (0:ℝ)..t₁, (1/d : ℝ) = t₁/d := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    have hone : ∀ t, 0 ≤ t → 1/(C * t ^ ((2:ℝ)/3)) = C⁻¹ * t ^ (-(2:ℝ)/3) := by
      intro t ht
      rw [show (-(2:ℝ))/3 = -((2:ℝ)/3) by ring, Real.rpow_neg ht (2/3), one_div, mul_inv]
    have hI2 : ∫ t in (0:ℝ)..t₁, 1/(C * t ^ ((2:ℝ)/3)) = 3 * t₁ ^ ((1:ℝ)/3)/C := by
      rw [intervalIntegral.integral_congr (g := fun t => C⁻¹ * t ^ (-(2:ℝ)/3)) (fun t ht => by
        rw [Set.uIcc_of_le ht₁pos.le] at ht
        exact hone t ht.1)]
      rw [rpow_neg_two_thirds_integral ht₁pos.le]
      ring
    have hA1 : t₁ / d = d^((1:ℝ)/2)/C^((3:ℝ)/2) := by
      rw [ht₁, show (3:ℝ)/2 = (1:ℝ)/2 + 1 by norm_num,
        Real.rpow_add (by positivity : (0:ℝ) < d/C), Real.rpow_one,
        Real.div_rpow hdnn hCpos.le]
      rw [Real.rpow_add hCpos, Real.rpow_one]
      field_simp
    have hA2 : 3 * t₁ ^ ((1:ℝ)/3)/C = 3 * d^((1:ℝ)/2)/C^((3:ℝ)/2) := by
      rw [ht₁, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ d/C)]
      norm_num
      rw [Real.div_rpow hdnn hCpos.le]
      rw [show (3:ℝ)/2 = (1:ℝ)/2 + 1 by norm_num, Real.rpow_add hCpos, Real.rpow_one]
      field_simp
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hKint C t₁ hCpos ht₁pos.le), hI1, hI2]
    rw [hA1, hA2]
    ring
  have hfinal : -2 * d^((1:ℝ)/2)/C^((3:ℝ)/2) ≤
      -d^((1:ℝ)/2) * (1 - c^2/C^2)/(2*C^((3:ℝ)/2)) + 2*d/(c*(T/2)^((2:ℝ)/3)) := by
    have hYnn : 0 ≤ d^((1:ℝ)/2)/C^((3:ℝ)/2) := by positivity
    have hcoef : -2 ≤ -(1 - c^2/C^2)/2 := by
      have : 0 ≤ c^2/C^2 := by positivity
      linarith
    have hA := mul_le_mul_of_nonneg_right hcoef hYnn
    have hB : 0 ≤ 2*d/(c*(T/2)^((2:ℝ)/3)) := by positivity
    have key : -2 * (d^((1:ℝ)/2)/C^((3:ℝ)/2)) ≤
        -(1 - c^2/C^2)/2 * (d^((1:ℝ)/2)/C^((3:ℝ)/2)) + 2*d/(c*(T/2)^((2:ℝ)/3)) := by
      linarith
    rw [show (-2:ℝ) * d^((1:ℝ)/2)/C^((3:ℝ)/2) = -2 * (d^((1:ℝ)/2)/C^((3:ℝ)/2)) by ring,
        show -d^((1:ℝ)/2) * (1 - c^2/C^2)/(2*C^((3:ℝ)/2)) =
          -(1 - c^2/C^2)/2 * (d^((1:ℝ)/2)/C^((3:ℝ)/2)) by ring]
    exact key
  calc ∫ t in (0:ℝ)..T, F t
      = (∫ t in (0:ℝ)..t₁, F t) + ∫ t in t₁..T, F t :=
        (intervalIntegral.integral_add_adjacent_intervals hF_int1 hF_int2).symm
    _ ≤ (∫ t in (0:ℝ)..t₁, (1/d - 1/(C * t ^ ((2:ℝ)/3)))) + 0 := add_le_add hstep1 hstep2
    _ = -2 * d^((1:ℝ)/2)/C^((3:ℝ)/2) := by rw [add_zero, hg_val]
    _ ≤ -d^((1:ℝ)/2) * (1 - c^2/C^2)/(2*C^((3:ℝ)/2)) + 2*d/(c*(T/2)^((2:ℝ)/3)) := hfinal


end Commons.Analysis.Integral