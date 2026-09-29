import Mathlib
import Submission.Work.TMComp.RealCartanDefs
import Submission.Work.TMComp.RealCartan.rcPot_integrable_iff
import Submission.Work.TMComp.RealCartan.rcPot_volume_lt_top
import Submission.Work.TMComp.RealCartan.rcPot_analyticAt_clog_neg

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace Work.TMComp.RealCartan



/-! ## Geometric preliminaries -/

lemma rcPot_norm_le_norm_sub_ofReal {v : ℂ} {r : ℝ} (hr : r ≤ 0) (hv : 0 ≤ v.re) :
    ‖v‖ ≤ ‖v - (r:ℂ)‖ := by
  have h1 : ‖v‖^2 ≤ ‖v - (r:ℂ)‖^2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h1

lemma rcPot_mem_slitPlane_of_mem_ball {v u : ℂ} {ρ : ℝ} (hv : 0 ≤ v.re) (hρ : ρ < ‖v‖)
    (hu : u ∈ ball v ρ) : u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hu' : u = ((u.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him, Complex.ofReal_re, Complex.ofReal_im]
  have h1 : ‖v‖ ≤ ‖v - ((u.re : ℝ) : ℂ)‖ := rcPot_norm_le_norm_sub_ofReal hre hv
  rw [← hu'] at h1
  have h2 : ‖v - u‖ < ρ := by
    have := mem_ball.1 hu
    rwa [dist_eq_norm, norm_sub_rev] at this
  linarith

/-! ## Kernel estimates -/

lemma rcPot_norm_clog_le (u : ℂ) : ‖Complex.log u‖ ≤ |Real.log ‖u‖| + Real.pi := by
  have h1 : ‖Complex.log u‖ ≤ |(Complex.log u).re| + |(Complex.log u).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 : |u.arg| ≤ Real.pi := Complex.abs_arg_le_pi u
  linarith

lemma rcPot_integrable_clog_of_integrable_log_norm {B : Set ℝ} {w : ℂ} (hvol : volume B ≠ ⊤)
    (h : Integrable (fun t : ℝ => Real.log ‖w - (t:ℂ)‖) (volume.restrict B)) :
    (Integrable (fun t : ℝ => Complex.log (w - (t:ℂ))) (volume.restrict B) ∧
     Integrable (fun t : ℝ => Complex.log ((t:ℂ) - w)) (volume.restrict B)) := by
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    (isFiniteMeasure_iff (volume.restrict B)).2 (by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact lt_top_iff_ne_top.2 hvol)
  have hmaj : Integrable (fun t : ℝ => |Real.log ‖w - (t:ℂ)‖| + Real.pi) (volume.restrict B) :=
    h.abs.add (integrable_const_iff.2 (Or.inr hfin))
  constructor
  · refine hmaj.mono' ((Complex.measurable_log.comp (measurable_const.sub
      Complex.continuous_ofReal.measurable))).aestronglyMeasurable ?_
    filter_upwards with t
    exact rcPot_norm_clog_le _
  · refine hmaj.mono' ((Complex.measurable_log.comp (Complex.continuous_ofReal.measurable.sub
      measurable_const))).aestronglyMeasurable ?_
    filter_upwards with t
    have h2 : ‖Complex.log ((t:ℂ) - w)‖ ≤ |Real.log ‖(t:ℂ) - w‖| + Real.pi := rcPot_norm_clog_le _
    rwa [norm_sub_rev] at h2

/-! ## Holomorphy of the two kernel integrals -/

theorem rcPot_analyticAt_clog {B : Set ℝ} {z : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hBm : MeasurableSet B) (hvol : volume B < ∞)
    (hsep : ∀ t ∈ B, ∀ w ∈ ball z ρ, δ ≤ ‖w - (t:ℂ)‖)
    (hslit : ∀ t ∈ B, ∀ w ∈ ball z ρ, (w - (t:ℂ)) ∈ Complex.slitPlane)
    (hint : ∀ w ∈ ball z ρ, Integrable (fun t : ℝ => Complex.log (w - (t:ℂ))) (volume.restrict B)) :
    AnalyticAt ℂ (fun w : ℂ => ∫ t in B, Complex.log (w - (t:ℂ))) z := by
  have hfin : IsFiniteMeasure (volume.restrict B) := by
    rw [isFiniteMeasure_iff]; simpa using hvol
  have hbound : Integrable (fun (_ : ℝ) => δ⁻¹) (volume.restrict B) := by
    rw [integrable_const_iff]; exact Or.inr hfin
  have key : ∀ w ∈ ball z ρ, HasDerivAt (fun w : ℂ => ∫ t in B, Complex.log (w - (t:ℂ)))
      (∫ t in B, (w - (t:ℂ))⁻¹) w := by
    intro w hw
    have hsw : ball z ρ ∈ 𝓝 w := IsOpen.mem_nhds isOpen_ball hw
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℂ) (E := ℂ) (α := ℝ) (μ := volume.restrict B)
      (F := fun (w : ℂ) (t : ℝ) => Complex.log (w - (t:ℂ)))
      (F' := fun (w : ℂ) (t : ℝ) => (w - (t:ℂ))⁻¹)
      (bound := fun _ => δ⁻¹) (x₀ := w) (s := ball z ρ)
      hsw ?_ (hint w hw) ?_ ?_ hbound ?_).2
    · filter_upwards [hsw] with x hx
      refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) hBm
      exact ((continuousAt_const.sub Complex.continuous_ofReal.continuousAt).clog
        (hslit t ht x hx)).continuousWithinAt
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) hBm
      refine ((ContinuousAt.inv₀ (continuousAt_const.sub
        Complex.continuous_ofReal.continuousAt) ?_)).continuousWithinAt
      intro hzero
      have h2 : ‖((fun x : ℝ => w) - Complex.ofReal) t‖ = 0 := by rw [hzero, norm_zero]
      have h1 : δ ≤ ‖((fun x : ℝ => w) - Complex.ofReal) t‖ := hsep t ht w hw
      linarith
    · rw [ae_restrict_iff' hBm]
      refine Eventually.of_forall fun t ht x hx => ?_
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le hδ (hsep t ht x hx)) hδ).2 (hsep t ht x hx)
    · rw [ae_restrict_iff' hBm]
      refine Eventually.of_forall fun t ht x hx => ?_
      have h1 : HasDerivAt Complex.log ((x - (t:ℂ))⁻¹) (x - (t:ℂ)) :=
        Complex.hasDerivAt_log (hslit t ht x hx)
      have h2 : HasDerivAt (fun w : ℂ => w - (t:ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).sub_const (t:ℂ)
      have h3 := h1.comp x h2
      simpa [Function.comp_def, mul_one] using h3
  refine DifferentiableOn.analyticAt (s := ball z ρ)
    (fun w hw => (key w hw).differentiableAt.differentiableWithinAt) ?_
  exact IsOpen.mem_nhds isOpen_ball (mem_ball_self hρ)

/-! ## Assembly -/

theorem rcPot_harmonic_of_pos {B : Set ℝ} (hB : IsClosed B) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∉ Complex.ofReal '' B) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Work.TMComp.RC.logPot B R w) z := by
  rcases B.eq_empty_or_nonempty with hBemp | hBne
  · subst hBemp
    have hzero : (fun w : ℂ => Work.TMComp.RC.logPot (∅ : Set ℝ) R w) = fun _ => (0:ℝ) := by
      funext w
      simp [Work.TMComp.RC.logPot]
    rw [hzero]
    exact InnerProductSpace.harmonicAt_const 0
  by_cases hint : Integrable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) (volume.restrict B)
  · -- ======== integrable case ========
    have hvol : volume B ≠ ⊤ := rcPot_volume_lt_top hB hR hint
    obtain ⟨d, hdpos, hdle⟩ := rcPot_dist_pos hB hz
    set ρ : ℝ := d / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hsep : ∀ t ∈ B, ∀ w ∈ ball z ρ, ρ ≤ ‖w - (t:ℂ)‖ := by
      intro t ht w hw
      have h1 : d ≤ ‖z - (t:ℂ)‖ := hdle t ht
      have h2 : ‖w - z‖ < ρ := by
        have := mem_ball.1 hw
        rwa [dist_eq_norm] at this
      have h3 : ‖z - (t:ℂ)‖ ≤ ‖z - w‖ + ‖w - (t:ℂ)‖ := by
        calc ‖z - (t:ℂ)‖ = ‖(z - w) + (w - (t:ℂ))‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w - (t:ℂ)‖ := norm_add_le _ _
      have h4 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev _ _
      rw [hρdef] at h2
      linarith
    set B₁ : Set ℝ := B ∩ Set.Iio z.re with hB₁def
    set B₂ : Set ℝ := B ∩ Set.Ici z.re with hB₂def
    have hB₁m : MeasurableSet B₁ := hB.measurableSet.inter measurableSet_Iio
    have hB₂m : MeasurableSet B₂ := hB.measurableSet.inter measurableSet_Ici
    have hsub₁ : B₁ ⊆ B := fun x hx => hx.1
    have hsub₂ : B₂ ⊆ B := fun x hx => hx.1
    have hdisj : Disjoint B₁ B₂ := by
      rw [hB₁def, hB₂def, Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici] at hx
      exact absurd hx.2.2 (not_le.2 hx.1.2)
    have hcov : B₁ ∪ B₂ = B := by
      rw [hB₁def, hB₂def, ← Set.inter_union_distrib_left, Set.Iio_union_Ici, Set.inter_univ]
    have hvol₁ : volume B₁ ≠ ⊤ := ne_top_of_le_ne_top hvol (measure_mono hsub₁)
    have hvol₂ : volume B₂ ≠ ⊤ := ne_top_of_le_ne_top hvol (measure_mono hsub₂)
    have hintw : ∀ w ∈ ball z ρ,
        Integrable (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖)) (volume.restrict B) := by
      intro w hw
      have hwS : w ∉ Complex.ofReal '' B := by
        intro hws
        obtain ⟨s, hs, hsw⟩ := hws
        have h1 : ρ ≤ ‖w - (s:ℂ)‖ := hsep s hs w hw
        rw [hsw, sub_self, norm_zero] at h1
        linarith
      exact (rcPot_integrable_iff hB hR hz hwS).1 hint
    have hlognorm : ∀ w ∈ ball z ρ,
        Integrable (fun t : ℝ => Real.log ‖w - (t:ℂ)‖) (volume.restrict B) := by
      intro w hw
      have hfw := hintw w hw
      have hconst : Integrable (fun _ : ℝ => Real.log R) (volume.restrict B) :=
        integrable_const_iff.2 (Or.inr ((isFiniteMeasure_iff (volume.restrict B)).2 (by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact lt_top_iff_ne_top.2 hvol)))
      have hsub : Integrable (fun t : ℝ => Real.log R - Real.log (R / ‖w - (t:ℂ)‖))
          (volume.restrict B) := hconst.sub hfw
      refine hsub.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hB.measurableSet] with t ht
      have hne : ‖w - (t:ℂ)‖ ≠ 0 := by
        intro h0
        have h1 := hsep t ht w hw
        rw [h0] at h1; linarith
      rw [Real.log_div hR.ne' hne]
      ring
    have hclog₁ : ∀ w ∈ ball z ρ,
        Integrable (fun t : ℝ => Complex.log (w - (t:ℂ))) (volume.restrict B₁) :=
      fun w hw => (rcPot_integrable_clog_of_integrable_log_norm hvol₁
        ((hlognorm w hw).mono_measure (Measure.restrict_mono_set volume hsub₁))).1
    have hclog₂ : ∀ w ∈ ball z ρ,
        Integrable (fun t : ℝ => Complex.log ((t:ℂ) - w)) (volume.restrict B₂) :=
      fun w hw => (rcPot_integrable_clog_of_integrable_log_norm hvol₂
        ((hlognorm w hw).mono_measure (Measure.restrict_mono_set volume hsub₂))).2
    have hslit₁ : ∀ t ∈ B₁, ∀ w ∈ ball z ρ, (w - (t:ℂ)) ∈ Complex.slitPlane := by
      intro t ht w hw
      obtain ⟨htB, htz⟩ := ht
      rw [Set.mem_Iio] at htz
      refine rcPot_mem_slitPlane_of_mem_ball (v := z - (t:ℂ)) (u := w - (t:ℂ)) (ρ := ρ) ?_ ?_ ?_
      · show 0 ≤ (z - (t:ℂ)).re
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith
      · have h1 : d ≤ ‖z - (t:ℂ)‖ := hdle t htB
        rw [hρdef]
        linarith
      · rw [mem_ball, dist_eq_norm]
        have h2 : dist w z < ρ := mem_ball.1 hw
        rw [dist_eq_norm] at h2
        have h3 : ‖(w - (t:ℂ)) - (z - (t:ℂ))‖ = ‖w - z‖ := by
          rw [sub_sub_sub_cancel_right]
        rw [h3]
        exact h2
    have hslit₂ : ∀ t ∈ B₂, ∀ w ∈ ball z ρ, ((t:ℂ) - w) ∈ Complex.slitPlane := by
      intro t ht w hw
      obtain ⟨htB, htz⟩ := ht
      rw [Set.mem_Ici] at htz
      refine rcPot_mem_slitPlane_of_mem_ball (v := (t:ℂ) - z) (u := (t:ℂ) - w) (ρ := ρ) ?_ ?_ ?_
      · show 0 ≤ ((t:ℂ) - z).re
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith
      · have h1 : d ≤ ‖z - (t:ℂ)‖ := hdle t htB
        rw [norm_sub_rev]
        rw [hρdef]
        linarith
      · rw [mem_ball, dist_eq_norm]
        have h2 : dist w z < ρ := mem_ball.1 hw
        rw [dist_eq_norm] at h2
        have h3 : ‖((t:ℂ) - w) - ((t:ℂ) - z)‖ = ‖z - w‖ := by
          rw [sub_sub_sub_cancel_left]
        rw [h3, norm_sub_rev]
        exact h2
    have hG₁ : AnalyticAt ℂ (fun w : ℂ => ∫ t in B₁, Complex.log (w - (t:ℂ))) z :=
      rcPot_analyticAt_clog hρpos hρpos hB₁m (lt_top_iff_ne_top.2 hvol₁)
        (fun t ht => hsep t ht.1) hslit₁ hclog₁
    have hG₂ : AnalyticAt ℂ (fun w : ℂ => ∫ t in B₂, Complex.log ((t:ℂ) - w)) z :=
      rcPot_analyticAt_clog_neg hρpos hρpos hB₂m hvol₂
        (fun t ht => hsep t ht.1) hslit₂ hclog₂
    have hG : AnalyticAt ℂ (fun w : ℂ => (∫ t in B₁, Complex.log (w - (t:ℂ)))
        + (∫ t in B₂, Complex.log ((t:ℂ) - w))) z := hG₁.add hG₂
    have hident : ∀ w ∈ ball z ρ,
        Work.TMComp.RC.logPot B R w
          = Real.log R * (volume B).toReal
            - ((∫ t in B₁, Complex.log (w - (t:ℂ)))
               + (∫ t in B₂, Complex.log ((t:ℂ) - w))).re := by
      intro w hw
      have hfB := hintw w hw
      have hgB := hlognorm w hw
      have hfB₁ : Integrable (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖)) (volume.restrict B₁) :=
        hfB.mono_measure (Measure.restrict_mono_set volume hsub₁)
      have hfB₂ : Integrable (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖)) (volume.restrict B₂) :=
        hfB.mono_measure (Measure.restrict_mono_set volume hsub₂)
      have hgB₁ : Integrable (fun t : ℝ => Real.log ‖w - (t:ℂ)‖) (volume.restrict B₁) :=
        hgB.mono_measure (Measure.restrict_mono_set volume hsub₁)
      have hgB₂ : Integrable (fun t : ℝ => Real.log ‖w - (t:ℂ)‖) (volume.restrict B₂) :=
        hgB.mono_measure (Measure.restrict_mono_set volume hsub₂)
      have hcl₁ := (rcPot_integrable_clog_of_integrable_log_norm hvol₁ hgB₁).1
      have hcl₂ := (rcPot_integrable_clog_of_integrable_log_norm hvol₂ hgB₂).2
      have hc₁ : Integrable (fun _ : ℝ => Real.log R) (volume.restrict B₁) :=
        integrable_const_iff.2 (Or.inr ((isFiniteMeasure_iff (volume.restrict B₁)).2 (by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact lt_top_iff_ne_top.2 hvol₁)))
      have hc₂ : Integrable (fun _ : ℝ => Real.log R) (volume.restrict B₂) :=
        integrable_const_iff.2 (Or.inr ((isFiniteMeasure_iff (volume.restrict B₂)).2 (by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact lt_top_iff_ne_top.2 hvol₂)))
      have hcg₁ : (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖))
          =ᵐ[volume.restrict B₁] (fun t : ℝ => Real.log R - Real.log ‖w - (t:ℂ)‖) := by
        filter_upwards [MeasureTheory.ae_restrict_mem hB₁m] with t ht
        have hne : ‖w - (t:ℂ)‖ ≠ 0 := by
          intro h0
          have h1 := hsep t ht.1 w hw
          rw [h0] at h1; linarith
        rw [Real.log_div hR.ne' hne]
      have e₁ : (∫ t in B₁, Real.log (R / ‖w - (t:ℂ)‖))
          = Real.log R * (volume B₁).toReal - ∫ t in B₁, Real.log ‖w - (t:ℂ)‖ := by
        rw [MeasureTheory.integral_congr_ae hcg₁, MeasureTheory.integral_sub hc₁ hgB₁,
          MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real_def]
        ring
      have hcg₂ : (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖))
          =ᵐ[volume.restrict B₂] (fun t : ℝ => Real.log R - Real.log ‖w - (t:ℂ)‖) := by
        filter_upwards [MeasureTheory.ae_restrict_mem hB₂m] with t ht
        have hne : ‖w - (t:ℂ)‖ ≠ 0 := by
          intro h0
          have h1 := hsep t ht.1 w hw
          rw [h0] at h1; linarith
        rw [Real.log_div hR.ne' hne]
      have e₂ : (∫ t in B₂, Real.log (R / ‖w - (t:ℂ)‖))
          = Real.log R * (volume B₂).toReal - ∫ t in B₂, Real.log ‖w - (t:ℂ)‖ := by
        rw [MeasureTheory.integral_congr_ae hcg₂, MeasureTheory.integral_sub hc₂ hgB₂,
          MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real_def]
        ring
      have f₁ : ((∫ t in B₁, Complex.log (w - (t:ℂ)))).re
          = ∫ t in B₁, Real.log ‖w - (t:ℂ)‖ := by
        rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hcl₁]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [Complex.reCLM_apply, Complex.log_re]
      have f₂ : ((∫ t in B₂, Complex.log ((t:ℂ) - w))).re
          = ∫ t in B₂, Real.log ‖w - (t:ℂ)‖ := by
        rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hcl₂]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [Complex.reCLM_apply, Complex.log_re, norm_sub_rev]
      have hv : (volume B₁).toReal + (volume B₂).toReal = (volume B).toReal := by
        rw [← ENNReal.toReal_add hvol₁ hvol₂, ← MeasureTheory.measure_union hdisj hB₂m, hcov]
      have e_split : (∫ t in B, Real.log (R / ‖w - (t:ℂ)‖))
          = (∫ t in B₁, Real.log (R / ‖w - (t:ℂ)‖))
            + (∫ t in B₂, Real.log (R / ‖w - (t:ℂ)‖)) := by
        rw [← hcov, MeasureTheory.setIntegral_union hdisj hB₂m hfB₁ hfB₂]
      rw [Work.TMComp.RC.logPot, e_split, e₁, e₂, Complex.add_re, f₁, f₂]
      have : Real.log R * (volume B₁).toReal + Real.log R * (volume B₂).toReal
          = Real.log R * (volume B).toReal := by rw [← mul_add, hv]
      linarith
    have hev : (fun w : ℂ => Work.TMComp.RC.logPot B R w) =ᶠ[𝓝 z]
        (fun w : ℂ => Real.log R * (volume B).toReal
          - ((∫ t in B₁, Complex.log (w - (t:ℂ)))
             + (∫ t in B₂, Complex.log ((t:ℂ) - w))).re) :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds z hρpos) hident
    refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
    have hfun2 : (fun w : ℂ => Real.log R * (volume B).toReal
          - ((∫ t in B₁, Complex.log (w - (t:ℂ)))
             + (∫ t in B₂, Complex.log ((t:ℂ) - w))).re)
        = (fun _ : ℂ => Real.log R * (volume B).toReal)
          - (fun w : ℂ => ((∫ t in B₁, Complex.log (w - (t:ℂ)))
             + (∫ t in B₂, Complex.log ((t:ℂ) - w))).re) := rfl
    rw [hfun2]
    exact (InnerProductSpace.harmonicAt_const (Real.log R * (volume B).toReal)).sub
      (AnalyticAt.harmonicAt_re hG)
  · -- ======== non-integrable case ========
    obtain ⟨d, hdpos, hdle⟩ := rcPot_dist_pos hB hz
    have hev : (fun w : ℂ => Work.TMComp.RC.logPot B R w) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hdpos) fun w hw => ?_
      have hwS : w ∉ Complex.ofReal '' B := by
        intro hws
        obtain ⟨s, hs, hsw⟩ := hws
        have h1 : d ≤ ‖z - (s:ℂ)‖ := hdle s hs
        have h2 : ‖w - z‖ < d := by
          have := mem_ball.1 hw
          rwa [dist_eq_norm] at this
        rw [hsw, norm_sub_rev] at h1
        linarith
      have hni : ¬ Integrable (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖)) (volume.restrict B) :=
        fun hc => hint ((rcPot_integrable_iff hB hR hwS hz).1 hc)
      change (∫ t in B, Real.log (R / ‖w - (t:ℂ)‖)) = 0
      exact integral_undef hni
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).2 (InnerProductSpace.harmonicAt_const 0)

theorem rcPot_harmonic {B : Set ℝ} (hB : IsClosed B) (R : ℝ) {z : ℂ}
    (hz : z ∉ (Complex.ofReal '' B)) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Work.TMComp.RC.logPot B R w) z := by
  rcases eq_or_ne R 0 with h0 | hne
  · subst h0
    have hzero : (fun w : ℂ => Work.TMComp.RC.logPot B 0 w) = fun _ => (0:ℝ) := by
      funext w
      simp [Work.TMComp.RC.logPot]
    rw [hzero]
    exact InnerProductSpace.harmonicAt_const 0
  · have hfun : (fun w : ℂ => Work.TMComp.RC.logPot B R w)
        = fun w : ℂ => Work.TMComp.RC.logPot B |R| w := by
      funext w
      change (∫ t in B, Real.log (R / ‖w - (t:ℂ)‖))
        = ∫ t in B, Real.log (|R| / ‖w - (t:ℂ)‖)
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with t
      rw [← Real.log_abs (R / ‖w - (t:ℂ)‖), abs_div, abs_of_nonneg (norm_nonneg _)]
    rw [hfun]
    exact rcPot_harmonic_of_pos hB (abs_pos.mpr hne) hz

end Work.TMComp.RealCartan
