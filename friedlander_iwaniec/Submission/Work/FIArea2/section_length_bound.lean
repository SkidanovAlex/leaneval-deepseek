import Mathlib
import Submission.Work.FIArea2.vol_bound_defs

set_option autoImplicit false

namespace Work.FIArea2

noncomputable section

open MeasureTheory

/-- Elementary inequality: for `0 ≤ b` and `0 < a`, `√b - √a ≤ (b - a)/(2√a)`. -/
lemma sl_sqrt_sub_sqrt_le_div (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    Real.sqrt b - Real.sqrt a ≤ (b - a) / (2 * Real.sqrt a) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt a)]
  nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb, sq_nonneg (Real.sqrt a - Real.sqrt b)]

/-- Regime I: for `|u| ≤ volR M` the section length is at most `√6 · volR M`. -/
lemma sl_section_le_regime_I (M C u : ℝ) (hM : 0 ≤ M) (hu : |u| ≤ volR M) :
    2 * (Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) -
         Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M))) ≤ Real.sqrt 6 * volR M := by
  have hR : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hvr_sq : volR M ^ 2 = 4 * Real.sqrt M := volR_sq M hM
  have hu2 : u ^ 2 ≤ 4 * Real.sqrt M := by
    have h1 : |u| ^ 2 ≤ volR M ^ 2 :=
      sq_le_sq.mpr (by rwa [abs_of_nonneg (volR_nonneg M), abs_abs])
    rwa [sq_abs, hvr_sq] at h1
  have hconst : Real.sqrt 6 * volR M = 2 * Real.sqrt (6 * Real.sqrt M) := by
    rw [volR, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
    conv_rhs => rw [← (show Real.sqrt 4 = (2 : ℝ) by norm_num)]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    ring_nf
  by_cases hb : 0 ≤ min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)
  · have hb_le : min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2) ≤ 6 * Real.sqrt M :=
      le_trans (min_le_left _ _) (by linarith)
    have hle : Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2))
        ≤ Real.sqrt (6 * Real.sqrt M) := Real.sqrt_le_sqrt hb_le
    have ha0 : 0 ≤ Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M)) := Real.sqrt_nonneg _
    linarith
  · have hb' : min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2) < 0 := not_le.mp hb
    have hz : Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hb'.le
    have ha0 : 0 ≤ Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M)) := Real.sqrt_nonneg _
    have hc : 0 ≤ Real.sqrt 6 * volR M :=
      mul_nonneg (Real.sqrt_nonneg 6) (volR_nonneg M)
    rw [hz]
    linarith

/-- Regime II: for `|u| ≥ volR M` the section length is at most `4√2 √M / |u|`. -/
lemma sl_section_le_regime_II (M C u : ℝ) (hM : 1 ≤ M) (hu : volR M ≤ |u|) :
    2 * (Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) -
         Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M)))
      ≤ 4 * Real.sqrt 2 * Real.sqrt M / |u| := by
  have hM0 : 0 ≤ M := by linarith
  have hRpos : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < M)
  have hvr_sq : volR M ^ 2 = 4 * Real.sqrt M := volR_sq M hM0
  have hu2 : 4 * Real.sqrt M ≤ u ^ 2 := by
    have h1 : volR M ^ 2 ≤ |u| ^ 2 :=
      sq_le_sq.mpr (by rwa [abs_of_nonneg (volR_nonneg M), abs_abs])
    rwa [sq_abs, hvr_sq] at h1
  have hA_eq : max 0 (u ^ 2 - 2 * Real.sqrt M) = u ^ 2 - 2 * Real.sqrt M :=
    max_eq_right (by linarith)
  have hApos : 0 < u ^ 2 - 2 * Real.sqrt M := by linarith
  have hA_nonneg : 0 ≤ u ^ 2 - 2 * Real.sqrt M := le_of_lt hApos
  have hvRpos : 0 < volR M := by
    rw [volR]; exact Real.sqrt_pos.mpr (by linarith)
  have huabs_pos : 0 < |u| := lt_of_lt_of_le hvRpos hu
  have hdenA : 0 < Real.sqrt (u ^ 2 - 2 * Real.sqrt M) := Real.sqrt_pos.mpr hApos
  have hden2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- |u| ≤ √2 · √(u² - 2√M)
  have hle2 : |u| ≤ Real.sqrt 2 * Real.sqrt (u ^ 2 - 2 * Real.sqrt M) := by
    have h2 : Real.sqrt (u ^ 2 / 2) ≤ Real.sqrt (u ^ 2 - 2 * Real.sqrt M) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_div (sq_nonneg u) 2, Real.sqrt_sq_eq_abs] at h2
    have := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
    rwa [mul_div_cancel₀ _ (ne_of_gt hden2)] at this
  -- 4√M / √A ≤ 4√2 √M / |u|
  have hkey : 4 * Real.sqrt M / Real.sqrt (u ^ 2 - 2 * Real.sqrt M)
      ≤ 4 * Real.sqrt 2 * Real.sqrt M / |u| := by
    rw [div_le_div_iff₀ hdenA huabs_pos]
    have h4 : 0 ≤ 4 * Real.sqrt M := by positivity
    have hstep := mul_le_mul_of_nonneg_left hle2 h4
    nlinarith [hstep]
  by_cases hb : 0 ≤ min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)
  · have hbs := sl_sqrt_sub_sqrt_le_div (u ^ 2 - 2 * Real.sqrt M)
      (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) hApos hb
    have hbm : min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2) - (u ^ 2 - 2 * Real.sqrt M)
        ≤ 4 * Real.sqrt M := by
      have := min_le_left (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2); linarith
    have hstep : (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2) - (u ^ 2 - 2 * Real.sqrt M))
          / (2 * Real.sqrt (u ^ 2 - 2 * Real.sqrt M))
        ≤ 4 * Real.sqrt M / (2 * Real.sqrt (u ^ 2 - 2 * Real.sqrt M)) :=
      div_le_div_of_nonneg_right hbm (by positivity)
    have hcomb : 2 * (Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) -
          Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M)))
        ≤ 2 * (4 * Real.sqrt M / (2 * Real.sqrt (u ^ 2 - 2 * Real.sqrt M))) := by
      rw [hA_eq]
      nlinarith [hbs, hstep]
    have heq : 2 * (4 * Real.sqrt M / (2 * Real.sqrt (u ^ 2 - 2 * Real.sqrt M)))
        = 4 * Real.sqrt M / Real.sqrt (u ^ 2 - 2 * Real.sqrt M) := by
      field_simp
    linarith [hcomb, heq, hkey]
  · have hb' : min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2) < 0 := not_le.mp hb
    have hz : Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hb'.le
    have ha0 : 0 ≤ Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M)) := Real.sqrt_nonneg _
    have hnn : 0 ≤ 4 * Real.sqrt 2 * Real.sqrt M / |u| := by
      apply div_nonneg <;> positivity
    rw [hz]
    linarith

theorem section_length_bound (M C u : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    2 * (Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) -
          Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M))) ≤ volBound M C u := by
  have hM0 : 0 ≤ M := by linarith
  have hT_nonneg : 0 ≤ volT M C := volT_nonneg M C
  by_cases hI : |u| ≤ volR M
  · -- Region 1: |u| ≤ volR M
    have hmem : u ∈ Set.Icc (-(volR M)) (volR M) := Set.mem_Icc.mpr (abs_le.mp hI)
    have hind2 : 0 ≤ (Set.Ioo (-(volT M C)) (-(volS M C))
        ∪ Set.Ioo (volS M C) (volT M C)).indicator
        (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|) u := by
      by_cases h : u ∈ Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C)
      · rw [Set.indicator_of_mem h]
        apply div_nonneg <;> positivity
      · rw [Set.indicator_of_notMem h]
    have hvb : Real.sqrt 6 * volR M ≤ volBound M C u := by
      simp only [volBound, Pi.add_apply]
      rw [Set.indicator_of_mem hmem]
      linarith
    exact le_trans (sl_section_le_regime_I M C u hM0 hI) hvb
  · have hI' : volR M < |u| := not_le.mp hI
    by_cases hII : |u| < volT M C
    · -- Region 2: volS < |u| < volT
      have hSlt : volS M C < |u| := lt_of_le_of_lt (volS_le_volR M C) hI'
      have hmem : u ∈ Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C) := by
        rcases lt_abs.mp hSlt with h | h
        · exact Or.inr ⟨h, (abs_lt.mp hII).2⟩
        · exact Or.inl ⟨(abs_lt.mp hII).1, by linarith⟩
      have hnot1 : u ∉ Set.Icc (-(volR M)) (volR M) := by
        intro h
        have := abs_le.mpr h
        linarith
      have hvb : volBound M C u = 4 * Real.sqrt 2 * Real.sqrt M / |u| := by
        simp only [volBound, Pi.add_apply]
        rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot1]
        ring
      rw [hvb]
      exact sl_section_le_regime_II M C u hM hI'.le
    · -- Region 3: |u| ≥ volT
      have hII' : volT M C ≤ |u| := not_lt.mp hII
      have hT_sq : volT M C ^ 2 = (C + 2 * Real.sqrt M) / 2 :=
        volT_sq M C (by positivity)
      have hu2T : (C + 2 * Real.sqrt M) / 2 ≤ u ^ 2 := by
        have h2 : volT M C ^ 2 ≤ |u| ^ 2 := by
          apply sq_le_sq.mpr
          rwa [abs_of_nonneg hT_nonneg, abs_abs]
        rwa [sq_abs, hT_sq] at h2
      have hb_le_a : min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)
          ≤ max 0 (u ^ 2 - 2 * Real.sqrt M) := by
        have h1 : C - u ^ 2 ≤ u ^ 2 - 2 * Real.sqrt M := by linarith
        exact le_trans (min_le_right _ _) (le_trans h1 (le_max_right _ _))
      have hzero : 2 * (Real.sqrt (min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)) -
          Real.sqrt (max 0 (u ^ 2 - 2 * Real.sqrt M))) ≤ 0 := by
        have := Real.sqrt_le_sqrt hb_le_a
        linarith
      exact le_trans hzero (volBound_nonneg M C u)

end

end Work.FIArea2
