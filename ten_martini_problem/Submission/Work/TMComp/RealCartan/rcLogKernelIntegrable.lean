import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set Filter

/-- The logarithmic kernel `t ↦ log ‖w - t‖` is integrable over any bounded subset of `ℝ`.
This is the essential content: the function is (up to a.e. equality and an additive constant)
the logarithm of the distance to a point, which blows up only logarithmically. -/
private lemma integrableOn_log_norm_sub {B : Set ℝ} (hB : Bornology.IsBounded B) (w : ℂ) :
    IntegrableOn (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) B volume := by
  -- The kernel is interval integrable on every interval, by meromorphicity of `t ↦ w - t`.
  have hII : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) volume a b := by
    intro a b
    apply MeromorphicOn.intervalIntegrable_log_norm
    have h1 : MeromorphicOn (fun t : ℝ => (t : ℂ)) (uIcc a b) :=
      (Complex.ofRealCLM.analyticOnNhd (uIcc a b)).meromorphicOn
    have h2 : MeromorphicOn (fun _ : ℝ => w) (uIcc a b) := MeromorphicOn.const w
    exact h2.sub h1
  obtain ⟨r, hr0, hr⟩ := hB.subset_closedBall_lt 0 0
  have hsub : B ⊆ Icc (-r) r := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ) r := hr hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx'
    exact abs_le.mp hx'
  have hle : -r ≤ r := by linarith
  have hIcc : IntegrableOn (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) (Icc (-r) r) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (f := fun t : ℝ => Real.log ‖w - (t : ℂ)‖) hle).mp (hII (-r) r)
  exact hIcc.mono_set hsub

theorem rcLogKernelIntegrable {B : Set ℝ} (hB : Bornology.IsBounded B) (R : ℝ) (w : ℂ) :
    MeasureTheory.Integrable (fun t : ℝ => Real.log (R / ‖w - (t : ℂ)‖))
      (MeasureTheory.volume.restrict B) := by
  by_cases hR : R = 0
  · subst hR
    have hfun : (fun t : ℝ => Real.log (0 / ‖w - (t : ℂ)‖)) = fun _ : ℝ => (0 : ℝ) := by
      funext t
      rw [zero_div, Real.log_zero]
    rw [hfun]
    exact (integrable_const_iff (μ := volume.restrict B) (c := (0 : ℝ))).mpr (Or.inl rfl)
  · have hmain : Integrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) (volume.restrict B) :=
      integrableOn_log_norm_sub hB w
    have hfin : IsFiniteMeasure (volume.restrict B) :=
      (isFiniteMeasure_restrict (μ := volume) (s := B)).mpr hB.measure_lt_top.ne
    have hconst : Integrable (fun _ : ℝ => Real.log |R|) (volume.restrict B) :=
      integrable_const_iff.mpr (Or.inr hfin)
    have hsub : Integrable
        (fun t : ℝ => Real.log |R| - Real.log ‖w - (t : ℂ)‖) (volume.restrict B) :=
      hconst.sub hmain
    have hpt : ∀ t : ℝ, ‖w - (t : ℂ)‖ ≠ 0 →
        Real.log |R| - Real.log ‖w - (t : ℂ)‖ = Real.log (R / ‖w - (t : ℂ)‖) := by
      intro t ht
      have hs0 : 0 ≤ ‖w - (t : ℂ)‖ := norm_nonneg _
      have h1 : Real.log (R / ‖w - (t : ℂ)‖) = Real.log |R / ‖w - (t : ℂ)‖| :=
        (Real.log_abs (R / ‖w - (t : ℂ)‖)).symm
      rw [h1, abs_div, abs_of_nonneg hs0]
      exact (Real.log_div (abs_ne_zero.mpr hR) ht).symm
    have hset : {t : ℝ | ¬ (Real.log |R| - Real.log ‖w - (t : ℂ)‖
          = Real.log (R / ‖w - (t : ℂ)‖))} ⊆ {t : ℝ | ‖w - (t : ℂ)‖ = 0} := by
      intro t ht
      by_contra h
      exact ht (hpt t h)
    have hnull : volume {t : ℝ | ‖w - (t : ℂ)‖ = 0} = 0 := by
      refine measure_mono_null ?_ (measure_singleton w.re)
      intro t ht
      have h1 : w = (t : ℂ) := sub_eq_zero.mp (norm_eq_zero.mp ht)
      have h2 : w.re = t := by simpa using congrArg Complex.re h1
      simp [h2]
    refine hsub.congr ?_
    have haev : Filter.Eventually
        (fun t : ℝ => Real.log |R| - Real.log ‖w - (t : ℂ)‖
          = Real.log (R / ‖w - (t : ℂ)‖))
        (MeasureTheory.ae (volume : MeasureTheory.Measure ℝ)) := by
      rw [MeasureTheory.ae_iff]
      exact measure_mono_null hset hnull
    exact MeasureTheory.ae_restrict_of_ae haev

end Work.TMComp.RealCartan
