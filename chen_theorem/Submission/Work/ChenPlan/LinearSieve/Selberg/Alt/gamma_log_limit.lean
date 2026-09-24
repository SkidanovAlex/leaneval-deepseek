import Mathlib
import Submission.Work.NumberTheory.Chen.ApSumTenth.eulerMascheroni_eq_integral

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-- The integrand of the compact piece in the integral representation of `γ`. -/
private def G0 (t : ℝ) : ℝ := (1 - Real.exp (-t)) / t

/-- The integrand of the tail piece in the integral representation of `γ`. -/
private def G1 (t : ℝ) : ℝ := Real.exp (-t) / t

private lemma G0_measurable : Measurable G0 := by
  unfold G0
  exact Measurable.div (measurable_const.sub (Real.continuous_exp.measurable.comp measurable_neg))
    measurable_id

private lemma G1_measurable : Measurable G1 := by
  unfold G1
  exact Measurable.div (Real.continuous_exp.measurable.comp measurable_neg) measurable_id

private lemma G0_continuousAt {x : ℝ} (hx : x ≠ 0) : ContinuousAt G0 x := by
  unfold G0
  refine ContinuousAt.div ?_ continuousAt_id hx
  exact ContinuousAt.sub continuousAt_const
    ((Real.continuous_exp.continuousAt).comp continuousAt_neg)

private lemma G1_continuousAt {x : ℝ} (hx : x ≠ 0) : ContinuousAt G1 x := by
  unfold G1
  refine ContinuousAt.div ?_ continuousAt_id hx
  exact (Real.continuous_exp.continuousAt).comp continuousAt_neg

private lemma inv_sub_G0 {x : ℝ} (hx : x ≠ 0) : x⁻¹ - G0 x = G1 x := by
  simp only [G0, G1]
  field_simp
  ring

private lemma integrableOn_G1 : IntegrableOn G1 (Ioi (1 : ℝ)) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (1 : ℝ)) :=
    integrableOn_exp_neg_Ioi 1
  refine Integrable.mono hexp G1_measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [G1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [abs_of_pos ht0, abs_of_nonneg (Real.exp_nonneg _), div_le_iff₀ ht0]
  calc Real.exp (-t) = Real.exp (-t) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-t) * t := mul_le_mul_of_nonneg_left (le_of_lt ht) (Real.exp_nonneg _)

private lemma integrableOn_G0_Ioc {x : ℝ} (_hx : 0 < x) : IntegrableOn G0 (Ioc (0 : ℝ) x) := by
  refine IntegrableOn.of_bound ?_ G0_measurable.aestronglyMeasurable 1 ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [G0]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1]
    have h1 : 0 ≤ 1 - Real.exp (-t) := by
      have := Real.exp_le_one_iff.mpr (by linarith [ht.1] : -t ≤ 0)
      linarith
    rw [abs_of_nonneg h1, div_le_one ht.1]
    have := Real.one_sub_le_exp_neg t
    linarith

private lemma intervalIntegrable_G0 {x : ℝ} (hx : 1 ≤ x) : IntervalIntegrable G0 volume (0 : ℝ) x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ x)]
  exact integrableOn_G0_Ioc (by linarith)

private lemma intervalIntegrable_G1 {L : ℝ} (hL : 1 ≤ L) : IntervalIntegrable G1 volume (1 : ℝ) L := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  refine (G1_continuousAt ?_).continuousWithinAt
  have h1 : (1 : ℝ) ≤ t := by
    rw [uIcc_of_le hL] at ht
    exact ht.1
  linarith

theorem gamma_log_limit :
    Filter.Tendsto (fun L : ℝ => Real.log L - ∫ s in (0 : ℝ)..L, (1 - Real.exp (-s))/s)
      Filter.atTop (nhds (-Real.eulerMascheroniConstant)) := by
  change Filter.Tendsto (fun L : ℝ => Real.log L - ∫ s in (0 : ℝ)..L, G0 s)
    Filter.atTop (nhds (-Real.eulerMascheroniConstant))
  have hgamma :
      Real.eulerMascheroniConstant
        = (∫ t in Set.Ioc (0 : ℝ) 1, G0 t) - ∫ t in Set.Ioi (1 : ℝ), G1 t :=
    Work.NumberTheory.Chen.ApSumTenth.eulerMascheroni_eq_integral
  set A : ℝ := ∫ t in Set.Ioc (0 : ℝ) 1, G0 t with hA
  set B : ℝ := ∫ t in Set.Ioi (1 : ℝ), G1 t with hB
  have hgamma' : Real.eulerMascheroniConstant = A - B := hgamma
  have hev : (fun L : ℝ => Real.log L - ∫ s in (0 : ℝ)..L, G0 s)
      =ᶠ[Filter.atTop] (fun L : ℝ => -A + ∫ s in (1 : ℝ)..L, G1 s) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) L,
        HasDerivAt (fun u : ℝ => Real.log u - ∫ t in (0 : ℝ)..u, G0 t) (G1 x) x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := by
        rw [uIcc_of_le hL] at hx
        exact hx.1
      have hx0 : x ≠ 0 := by linarith
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
      have hint : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, G0 t) (G0 x) x :=
        intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_G0 hx1)
          (G0_measurable.aestronglyMeasurable.stronglyMeasurableAtFilter) (G0_continuousAt hx0)
      have h := hlog.sub hint
      rw [inv_sub_G0 hx0] at h
      exact h
    have hG1i : IntervalIntegrable G1 volume (1 : ℝ) L := intervalIntegrable_G1 hL
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hG1i
    have h01 : (∫ t in (0 : ℝ)..1, G0 t) = A := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [Real.log_one, h01] at hftc
    linarith [hftc]
  have hlim : Filter.Tendsto (fun L : ℝ => -A + ∫ s in (1 : ℝ)..L, G1 s)
      Filter.atTop (nhds (-A + B)) := by
    have h := intervalIntegral_tendsto_integral_Ioi (μ := volume) (f := G1) (1 : ℝ)
      integrableOn_G1 tendsto_id
    simpa [hB] using tendsto_const_nhds.add h
  have hmain := Filter.Tendsto.congr' hev.symm hlim
  have hval : -A + B = -Real.eulerMascheroniConstant := by
    rw [hgamma']; ring
  rw [hval] at hmain
  exact hmain

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
