/-
# The volume of the region (7.4) of *FI* §7 — the "trivial" bound of Lemma 7.1

This module proves `Work.FIArea2.lemma_7_1_volume`:

  `∫_{ℝ²} 1_{M/4 ≤ g(t₁,t₂) ≤ 4M} = O(√M log(2 + 1/(1−γ²)))`,

for `g(t₁,t₂) = t₁⁴ − 2γt₁²t₂² + t₂⁴`, `1 ≤ M`, `0 ≤ γ < 1` (explicitly with constant `30`).  It is
the `‖F‖ ≤ C√M log(2 + δ^{-2})` bound of *FI* Lemma 7.1, used together with the two
integration-by-parts bounds of `Work.FIArea2.lemma_7_1_deriv4_bound`.

**Argument.**  Write `δ = √(1−γ²)`.  By `Work.FIArea2.region_bounds` (the ellipse bounds (7.3)) the
region is contained in the *square annulus*

  `S = {|t₁² − t₂²| ≤ 2√M} ∩ {t₁² + t₂² ≤ C}`,   `C = 4√M/δ`.

Fubini (`Work.FIArea2.volume_bigS_eq`) turns `volume S` into `∫ u, (length of the u-section)`, and
the `u`-section is `{t : a(u) ≤ t² ≤ b(u)}` with `a(u) = max 0 (u²−2√M)`,
`b(u) = min (u²+2√M) (C−u²)` (`Work.FIArea2.section_set_eq`), of length
`2(√b − √a) = volume {t : a ≤ t² ≤ b}` (`Work.FIArea6b.sq_section_measure`).  The elementary
estimate `Work.FIArea2.section_length_bound` shows this length is at most `volBound M C u`
(`Work.FIArea2.vol_bound_defs`): `√6·√(4√M)` for `|u| ≤ min (√(4√M)) √((C+2√M)/2)`,
`4√2√M/|u|` for `min (√(4√M)) √((C+2√M)/2) < |u| < √((C+2√M)/2)`, and `0` beyond (where the section
is empty).  Integrating `volBound` gives

  `volume R ≤ 8√6 √M + 8√2 √M log(T/s)`,  `T = √((C+2√M)/2)`, `s = min (√(4√M)) T`,

because the `1/|u|`-part contributes the annular integral
`Work.FIArea2.abs_inv_annulus_integral` (`∫ 1/|u| = 2 log(T/s)`); finally
`Work.FIArea2.log_volT_div_volS_le` gives `log(T/s) ≤ (1/4) log(1/(1−γ²))` (as `T²/s² ≤ 1/δ`), and
the elementary `Work.FIArea2.log_volume_arithmetic` absorbs the constants:
`8√6 √M + 2√2 √M log(1/(1−γ²)) ≤ 30 √M log(2 + 1/(1−γ²))`.  The final bridge from the Bochner
integral of the indicator to `(volume R).toReal` is `MeasureTheory.integral_indicator_const`.
-/
import Mathlib
import Submission.Work.FIArea2.vol_bound_defs
import Submission.Work.FIArea2.lemma_7_1_aux
import Submission.Work.FIArea2.section_set_eq
import Submission.Work.FIArea2.section_length_bound
import Submission.Work.FIArea2.abs_inv_annulus_integral
import Submission.Work.FIArea2.log_volume_arithmetic
import Submission.Work.FIArea2.log_volT_div_volS_le
import Submission.Work.FIArea2.integrable_volBound
import Submission.Work.FIArea6b.sq_section_measure

set_option autoImplicit false

namespace Work.FIArea2

noncomputable section

open MeasureTheory

/-! ## The two sets -/

/-- The region (7.4) of Lemma 7.1. -/
def regV (M γ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | M / 4 ≤ gq γ p.1 p.2 ∧ gq γ p.1 p.2 ≤ 4 * M}

/-- A containing "square annulus" set. -/
def bigS (M C : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | |p.1 ^ 2 - p.2 ^ 2| ≤ 2 * Real.sqrt M ∧ p.1 ^ 2 + p.2 ^ 2 ≤ C}

/-! ## From the region to the square annulus -/

theorem regV_subset_bigS (M γ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    regV M γ ⊆ bigS M (4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) := by
  intro p hp
  obtain ⟨h1, h2⟩ := hp
  have h3 := region_bounds M γ p.1 p.2 hM hγ0 hγ1 h1 h2
  exact ⟨h3.1, h3.2.2⟩

lemma measurableSet_regV (M γ : ℝ) : MeasurableSet (regV M γ) := by
  have h : Continuous fun p : ℝ × ℝ => gq γ p.1 p.2 := by
    simp only [gq]; fun_prop
  exact ((isClosed_le continuous_const h).inter (isClosed_le h continuous_const)).measurableSet

lemma isClosed_bigS (M C : ℝ) : IsClosed (bigS M C) := by
  have h1 : Continuous fun p : ℝ × ℝ => |p.1 ^ 2 - p.2 ^ 2| := by fun_prop
  have h2 : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  exact (isClosed_le h1 continuous_const).inter (isClosed_le h2 continuous_const)

/-! ## Fubini -/

theorem volume_bigS_eq (M C : ℝ) :
    volume (bigS M C)
      = ∫⁻ u, volume {t : ℝ | |u ^ 2 - t ^ 2| ≤ 2 * Real.sqrt M ∧ u ^ 2 + t ^ 2 ≤ C} := by
  have hmeas : MeasurableSet (bigS M C) := (isClosed_bigS M C).measurableSet
  change (volume.prod volume : Measure (ℝ × ℝ)) (bigS M C) = _
  rw [Measure.prod_apply hmeas]
  apply lintegral_congr
  intro u
  congr 1

/-! ## The section bound -/

theorem sec_volume_le (M C u : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    volume {t : ℝ | |u ^ 2 - t ^ 2| ≤ 2 * Real.sqrt M ∧ u ^ 2 + t ^ 2 ≤ C}
      ≤ ENNReal.ofReal (volBound M C u) := by
  rw [section_set_eq M C u]
  set a : ℝ := max 0 (u ^ 2 - 2 * Real.sqrt M) with ha_def
  set b : ℝ := min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2) with hb_def
  by_cases hab : a ≤ b
  · have ha0 : 0 ≤ a := by rw [ha_def]; exact le_max_left _ _
    rw [Work.FIArea6b.sq_section_measure ha0 hab]
    exact ENNReal.ofReal_le_ofReal (section_length_bound M C u hM hC)
  · have hempty : {t : ℝ | a ≤ t ^ 2 ∧ t ^ 2 ≤ b} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hab (le_trans h.1 h.2)
    rw [hempty, measure_empty]
    exact zero_le

/-! ## Integrability of the two pieces and the integral of `volBound` -/

lemma measurableSet_volAnn (M C : ℝ) :
    MeasurableSet (Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C)) :=
  measurableSet_Ioo.union measurableSet_Ioo

lemma integrable_volBound_first (M C : ℝ) :
    Integrable ((Set.Icc (-(volR M)) (volR M)).indicator (fun _ => Real.sqrt 6 * volR M)) := by
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  exact MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

lemma integrable_volBound_second (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    Integrable ((Set.Ioo (-(volT M C)) (-(volS M C)) ∪
        Set.Ioo (volS M C) (volT M C)).indicator
      (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|)) := by
  set A := Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C) with hA
  have hAmeas : MeasurableSet A := measurableSet_Ioo.union measurableSet_Ioo
  have hspos : 0 < volS M C := volS_pos M C (by linarith) (by positivity)
  have hsT : volS M C ≤ volT M C := volS_le_volT M C
  have hTnonneg : 0 ≤ volT M C := volT_nonneg M C
  rw [MeasureTheory.integrable_indicator_iff hAmeas]
  refine MeasureTheory.IntegrableOn.of_bound ?hfin ?haesm
    (4 * Real.sqrt 2 * Real.sqrt M / volS M C) ?hbd
  · -- finite measure of the annulus
    have hsub : A ⊆ Set.Icc (-(volT M C)) (volT M C) := by
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨h1, h2⟩ := hx
        exact ⟨le_of_lt h1, by linarith [le_of_lt h2, hspos]⟩
      · obtain ⟨h1, h2⟩ := hx
        exact ⟨by linarith [h1, hspos], le_of_lt h2⟩
    have hfinA : volume A ≤ volume (Set.Icc (-(volT M C)) (volT M C)) := measure_mono hsub
    rw [Real.volume_Icc] at hfinA
    exact lt_of_le_of_lt hfinA ENNReal.ofReal_lt_top
  · exact (Measurable.div measurable_const measurable_abs).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' hAmeas]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hxabs : volS M C ≤ |x| := by
      rcases hx with hx | hx
      · obtain ⟨h1, h2⟩ := hx
        rw [abs_of_neg (by linarith [h2, hspos])]
        linarith
      · obtain ⟨h1, h2⟩ := hx
        rw [abs_of_pos (by linarith [h1, hspos])]
        linarith
    have hcnonneg : 0 ≤ 4 * Real.sqrt 2 * Real.sqrt M :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) (Real.sqrt_nonneg M)
    have hnorm : ‖(4 * Real.sqrt 2 * Real.sqrt M / |x| : ℝ)‖
        = 4 * Real.sqrt 2 * Real.sqrt M / |x| := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hcnonneg (abs_nonneg x))]
    rw [hnorm]
    exact div_le_div_of_nonneg_left hcnonneg hspos hxabs

lemma integral_volBound_first (M C : ℝ) (hM0 : 0 ≤ M) :
    ∫ x, (Set.Icc (-(volR M)) (volR M)).indicator (fun _ => Real.sqrt 6 * volR M) x
      = 8 * Real.sqrt 6 * Real.sqrt M := by
  rw [MeasureTheory.integral_indicator_const (Real.sqrt 6 * volR M) measurableSet_Icc]
  rw [MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [volR_nonneg M])]
  rw [smul_eq_mul]
  have h2 : volR M ^ 2 = 4 * Real.sqrt M := volR_sq M hM0
  have h3 : 0 ≤ volR M := volR_nonneg M
  nlinarith [h2, h3, Real.sqrt_nonneg M, Real.sqrt_nonneg 6]

lemma integral_volBound_second (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∫ x, (Set.Ioo (-(volT M C)) (-(volS M C)) ∪
        Set.Ioo (volS M C) (volT M C)).indicator
      (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|) x
      = 8 * Real.sqrt 2 * Real.sqrt M * Real.log (volT M C / volS M C) := by
  have hAmeas : MeasurableSet (Set.Ioo (-(volT M C)) (-(volS M C)) ∪
      Set.Ioo (volS M C) (volT M C)) := measurableSet_Ioo.union measurableSet_Ioo
  have hspos : 0 < volS M C := volS_pos M C (by linarith) (by positivity)
  have hsT : volS M C ≤ volT M C := volS_le_volT M C
  have hkey : ∫ x in Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C),
      |x|⁻¹ = 2 * Real.log (volT M C / volS M C) :=
    abs_inv_annulus_integral (volS M C) (volT M C) hspos hsT
  have hstep : ∫ x, (Set.Ioo (-(volT M C)) (-(volS M C)) ∪
        Set.Ioo (volS M C) (volT M C)).indicator
      (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|) x
      = (4 * Real.sqrt 2 * Real.sqrt M) *
        ∫ x in Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C),
          |x|⁻¹ := by
    rw [MeasureTheory.integral_indicator hAmeas]
    rw [← MeasureTheory.integral_const_mul]
    simp only [div_eq_mul_inv]
  rw [hstep, hkey]
  ring

lemma integral_volBound_le (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∫ x, volBound M C x ≤ 8 * Real.sqrt 6 * Real.sqrt M
      + 8 * Real.sqrt 2 * Real.sqrt M * Real.log (volT M C / volS M C) := by
  have hsplit : ∫ x, volBound M C x
      = (∫ x, (Set.Icc (-(volR M)) (volR M)).indicator (fun _ => Real.sqrt 6 * volR M) x)
        + (∫ x, (Set.Ioo (-(volT M C)) (-(volS M C)) ∪
            Set.Ioo (volS M C) (volT M C)).indicator
          (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|) x) := by
    rw [volBound]
    exact MeasureTheory.integral_add (integrable_volBound_first M C)
      (integrable_volBound_second M C hM hC)
  rw [hsplit, integral_volBound_first M C (by linarith), integral_volBound_second M C hM hC]

/-! ## The main theorem -/

theorem lemma_7_1_volume (M γ : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∫ p : ℝ × ℝ, Set.indicator
        {p : ℝ × ℝ | M / 4 ≤ p.1 ^ 4 - 2 * γ * p.1 ^ 2 * p.2 ^ 2 + p.2 ^ 4 ∧
          p.1 ^ 4 - 2 * γ * p.1 ^ 2 * p.2 ^ 2 + p.2 ^ 4 ≤ 4 * M}
        (fun _ => (1 : ℝ)) p
      ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hδpos : 0 < Real.sqrt (1 - γ ^ 2) :=
    Real.sqrt_pos.mpr (one_sub_gamma_sq_pos γ hγ0 hγ1)
  change ∫ p : ℝ × ℝ, (regV M γ).indicator (fun _ => (1 : ℝ)) p
      ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) (measurableSet_regV M γ), smul_eq_mul, mul_one,
    MeasureTheory.measureReal_def]
  set C : ℝ := 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) with hC_def
  have hC0 : 0 ≤ C := by rw [hC_def]; positivity
  have hsub : regV M γ ⊆ bigS M C := by
    rw [hC_def]
    exact regV_subset_bigS M γ hMpos hγ0 hγ1
  refine ENNReal.toReal_le_of_le_ofReal ?hnn ?hle
  · have h1 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
    have h2 : 0 < Real.log (2 + 1 / (1 - γ ^ 2)) := by
      apply Real.log_pos
      have := div_pos one_pos (one_sub_gamma_sq_pos γ hγ0 hγ1)
      linarith
    positivity
  · have h4 : ∫ u, volBound M C u ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
      have hlog := log_volT_div_volS_le M γ hM hγ0 hγ1
      rw [← hC_def] at hlog
      have hmul : 8 * Real.sqrt 2 * Real.sqrt M * Real.log (volT M C / volS M C)
          ≤ 8 * Real.sqrt 2 * Real.sqrt M * ((1 / 4) * Real.log (1 / (1 - γ ^ 2))) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have hInt := integral_volBound_le M C hM hC0
      have hArith := log_volume_arithmetic M γ hM hγ0 hγ1
      linarith
    calc volume (regV M γ) ≤ volume (bigS M C) := measure_mono hsub
      _ ≤ ∫⁻ u, ENNReal.ofReal (volBound M C u) := by
          rw [volume_bigS_eq M C]
          exact lintegral_mono (fun u => sec_volume_le M C u hM hC0)
      _ = ENNReal.ofReal (∫ u, volBound M C u) :=
          (ofReal_integral_eq_lintegral_ofReal (integrable_volBound M C hM hC0)
            (Filter.Eventually.of_forall (fun u => volBound_nonneg M C u))).symm
      _ ≤ ENNReal.ofReal (30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) :=
          ENNReal.ofReal_le_ofReal h4

end
end Work.FIArea2
