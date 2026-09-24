import Mathlib

namespace Work.NumberTheory.Chen.ApSumTenth

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The integrand `(e^{-t} - 1)/t`, with the removable singularity at `0` set to `0`. -/
private def hr (t : ℝ) : ℝ := (Real.exp (-t) - 1) / t

private lemma measurable_hr : Measurable hr :=
  ((Real.measurable_exp.comp measurable_neg).sub measurable_const).div measurable_id

private lemma norm_hr_le_one {x : ℝ} (hx : 0 ≤ x) : ‖hr x‖ ≤ 1 := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · subst hx0
    simp [hr]
  · have hnum : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hle : hr x ≤ 0 := by
      simp only [hr]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hxpos)
    have hval : ‖hr x‖ = (1 - Real.exp (-x)) / x := by
      rw [Real.norm_of_nonpos hle]
      simp only [hr]
      ring
    rw [hval, div_le_one hxpos]
    linarith [Real.one_sub_le_exp_neg x]

private lemma integrableOn_hr_Icc : IntegrableOn hr (Set.Icc (0 : ℝ) 1) volume := by
  refine IntegrableOn.of_bound ?_ ?_ 1 ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  · exact measurable_hr.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact norm_hr_le_one hx.1

private lemma intervalIntegrable_hr (a b : ℝ) (h : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable hr volume a b := by
  rw [intervalIntegrable_iff]
  exact integrableOn_hr_Icc.mono_set h

/-- The primitive `p ↦ ∫_0^p (e^{-q}-1)/q` tends to `0` as `p → 0⁺`. -/
private lemma tendsto_integral_hr_zero :
    Tendsto (fun p : ℝ => ∫ q in (0 : ℝ)..p, hr q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbdd : ∀ᶠ p in 𝓝[>] (0 : ℝ), ‖∫ q in (0 : ℝ)..p, hr q‖ ≤ |p| := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with p hp
    have hb : ∀ x ∈ Set.uIoc (0 : ℝ) p, ‖hr x‖ ≤ 1 := by
      intro x hx
      have hx0 : 0 ≤ x := by
        rcases Set.mem_uIoc.mp hx with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact le_of_lt h1
        · linarith [hp.1]
      exact norm_hr_le_one hx0
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := p) hb
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun p => norm_nonneg _)) hbdd ?_
  simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- For `0 < p ≤ 1`, the interval integral from `1` to `p` splits at `0`. -/
private lemma integral_one_to_p_hr {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∫ q in (1 : ℝ)..p, hr q = (∫ q in (0 : ℝ)..p, hr q) - ∫ q in (0 : ℝ)..1, hr q := by
  have h01 : IntervalIntegrable hr volume (0 : ℝ) 1 :=
    intervalIntegrable_hr 0 1 (by
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Set.Ioc_subset_Icc_self)
  have h0p : IntervalIntegrable hr volume (0 : ℝ) p :=
    intervalIntegrable_hr 0 p (by
      rw [Set.uIoc_of_le hp.le]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hp1))
  have h := intervalIntegral.integral_interval_sub_left h01 h0p
  rw [intervalIntegral.integral_symm p 1]
  rw [← h]
  ring

/-- For `p > 0`, `∫_1^p e^{-q}/q - log p = ∫_1^p (e^{-q}-1)/q`. -/
private lemma key_identity {p : ℝ} (hp : 0 < p) :
    (∫ q in (1 : ℝ)..p, Real.exp (-q) / q) - Real.log p = ∫ q in (1 : ℝ)..p, hr q := by
  have hmem : ∀ q ∈ Set.uIcc (1 : ℝ) p, q ≠ 0 := by
    intro q hq
    have hq0 : 0 < q := by
      rcases Set.mem_uIcc.mp hq with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    exact ne_of_gt hq0
  have hcongr : ∫ q in (1 : ℝ)..p, Real.exp (-q) / q
      = ∫ q in (1 : ℝ)..p, (hr q + 1 / q) := by
    apply intervalIntegral.integral_congr
    intro q hq
    have hq0 := hmem q hq
    simp only [hr]
    field_simp
    ring
  have hint1 : IntervalIntegrable hr volume (1 : ℝ) p := by
    apply ContinuousOn.intervalIntegrable
    intro q hq
    have hq0 := hmem q hq
    refine ContinuousAt.continuousWithinAt ?_
    exact (((Real.continuous_exp.continuousAt.comp (continuous_neg.continuousAt)).sub
      (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) q)).div continuousAt_id hq0)
  have hint2 : IntervalIntegrable (fun q : ℝ => 1 / q) volume (1 : ℝ) p := by
    apply ContinuousOn.intervalIntegrable
    intro q hq
    have hq0 := hmem q hq
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) q).div continuousAt_id hq0
  rw [hcongr, intervalIntegral.integral_add hint1 hint2]
  rw [integral_one_div_of_pos one_pos hp, div_one]
  ring

theorem eulerMascheroni_limit_form
    (h1 : Real.eulerMascheroniConstant
      = (∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t)
        - (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)) :
    Filter.Tendsto
      (fun p : ℝ => (∫ q in (1 : ℝ)..p, Real.exp (-q) / q) - Real.log p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Real.eulerMascheroniConstant + ∫ q in Set.Ioi (1 : ℝ), Real.exp (-q) / q)) := by
  have hA : Real.eulerMascheroniConstant + (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)
      = ∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t := by linarith [h1]
  have hA' : (∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t)
      = -∫ t in (0 : ℝ)..1, hr t := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    simp only [hr]
    field_simp
    ring
  rw [hA, hA']
  have hlim : Tendsto (fun p : ℝ => ∫ q in (1 : ℝ)..p, hr q) (𝓝[>] (0 : ℝ))
      (𝓝 (-∫ q in (0 : ℝ)..1, hr q)) := by
    have hdec : ∀ᶠ p in 𝓝[>] (0 : ℝ), (∫ q in (0 : ℝ)..p, hr q) - ∫ q in (0 : ℝ)..1, hr q
        = ∫ q in (1 : ℝ)..p, hr q := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with p hp
      exact (integral_one_to_p_hr hp.1 hp.2.le).symm
    have hg : Tendsto (fun p : ℝ => (∫ q in (0 : ℝ)..p, hr q) - ∫ q in (0 : ℝ)..1, hr q)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 - ∫ q in (0 : ℝ)..1, hr q)) :=
      tendsto_integral_hr_zero.sub tendsto_const_nhds
    have := hg.congr' hdec
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with p hp
  exact (key_identity hp.1).symm

end

end Work.NumberTheory.Chen.ApSumTenth
