import Mathlib
import Submission.Work.TMComp.RealCartanDefs
import Submission.Work.TMComp.RealCartan.rcLogKernelIntegrable
import Submission.Work.TMComp.RealCartan.rcLogKernelIntegralOn
import Submission.Work.TMComp.RealCartan.rcTruncContinuous

/-!
# Continuity of the logarithmic potential `RC.logPot`

`RC.logPot B R z = ∫_{t ∈ B} log (R / ‖z - t‖) dt` has a singularity in the integrand at
`t = z` which *moves with* `z`; consequently there is no `z`-independent dominating function
and the dominated convergence theorem does not apply directly.

We regularise: for `ε > 0` put

`truncPot B R ε z = ∫_{t ∈ B} log (R / max ‖z - t‖ ε) dt`,

whose integrand is bounded on `B` (which is assumed bounded, hence of finite measure) and
continuous in `z`, so `z ↦ truncPot B R ε z` is continuous.  The error is

`logPot B R z - truncPot B R ε z = ∫_{t ∈ B, ‖z-t‖ < ε} log (ε / ‖z - t‖) dt`,

and since `‖z - t‖ ≥ |t - z.re|` this is at most
`∫_{-ε}^{ε} |log (|u| / ε)| du = 2 ε`, uniformly in `z`.  Letting `ε → 0` gives continuity.
-/

open MeasureTheory Filter Topology Set Bornology
open scoped ENNReal

noncomputable section

namespace Work.TMComp.RealCartan

/-- The truncated logarithmic potential of `B` at level `ε`: the log-kernel with its
singularity cut off at distance `ε` from `z`. -/
def truncPot (B : Set ℝ) (R ε : ℝ) (z : ℂ) : ℝ :=
  ∫ t in B, Real.log (R / max ‖z - (t : ℂ)‖ ε)

lemma ae_ne_restrict (B : Set ℝ) (c : ℝ) : ∀ᵐ t ∂(volume.restrict B), t ≠ c := by
  rw [ae_iff]
  have h : {t : ℝ | ¬ t ≠ c} = {c} := by ext t; simp
  rw [h, Measure.restrict_apply (MeasurableSet.singleton c)]
  exact measure_mono_null Set.inter_subset_left (measure_singleton c)

lemma continuous_truncKernel {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (z : ℂ) :
    Continuous (fun t : ℝ => Real.log (R / max ‖z - (t : ℂ)‖ ε)) := by
  have hden : Continuous (fun t : ℝ => max ‖z - (t : ℂ)‖ ε) :=
    (continuous_norm.comp (continuous_const.sub Complex.continuous_ofReal)).max continuous_const
  have hdenpos : ∀ t : ℝ, (0 : ℝ) < max ‖z - (t : ℂ)‖ ε :=
    fun t => lt_of_lt_of_le hε (le_max_right _ _)
  exact Continuous.log
    (Continuous.div continuous_const hden (fun t => ne_of_gt (hdenpos t)))
    (fun t => ne_of_gt (div_pos hR (hdenpos t)))

/-- The pointwise (a.e.) comparison behind the truncation-error bound: away from `t = z.re`
the difference of the two kernels is bounded by the `J`-supported profile
`|log (|t - z.re| / ε)|`, with `J = (z.re - ε, z.re + ε]`. -/
lemma abs_logKernel_sub_truncKernel_le {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (z : ℂ)
    {t : ℝ} (ht : t ≠ z.re) :
    |Real.log (R / ‖z - (t : ℂ)‖) - Real.log (R / max ‖z - (t : ℂ)‖ ε)|
      ≤ (Set.Ioc (z.re - ε) (z.re + ε)).indicator
          (fun t => |Real.log (|t - z.re| / ε)|) t := by
  by_cases hlt : ‖z - (t : ℂ)‖ < ε
  · have hpos : 0 < ‖z - (t : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h0
      apply ht
      have h1 : (z - (t : ℂ)).re = 0 := by rw [h0]; simp
      simp only [Complex.sub_re, Complex.ofReal_re] at h1
      linarith
    have habs_re : |t - z.re| ≤ ‖z - (t : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (z - (t : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h
      rw [abs_sub_comm]; exact h
    have hmem : t ∈ Set.Ioc (z.re - ε) (z.re + ε) := by
      have h' : |t - z.re| < ε := lt_of_le_of_lt habs_re hlt
      have h'' := abs_lt.mp h'
      exact ⟨by linarith [h''.1], by linarith [h''.2]⟩
    rw [Set.indicator_of_mem hmem, max_eq_right hlt.le]
    rw [Real.log_div (ne_of_gt hR) (ne_of_gt hpos),
      Real.log_div (ne_of_gt hR) (ne_of_gt hε)]
    have hposabs : 0 < |t - z.re| := abs_pos.mpr (sub_ne_zero.mpr ht)
    have hdiv : |t - z.re| / ε ≤ 1 := by
      rw [div_le_one hε]; exact le_of_lt (lt_of_le_of_lt habs_re hlt)
    have hlog_nonpos : Real.log (|t - z.re| / ε) ≤ 0 :=
      Real.log_nonpos (div_nonneg (abs_nonneg _) hε.le) hdiv
    have hle : Real.log |t - z.re| ≤ Real.log ‖z - (t : ℂ)‖ := Real.log_le_log hposabs habs_re
    have hnn : 0 ≤ Real.log ε - Real.log ‖z - (t : ℂ)‖ := by
      have h2 : Real.log ‖z - (t : ℂ)‖ ≤ Real.log ε := Real.log_le_log hpos hlt.le
      linarith
    rw [show Real.log R - Real.log ‖z - (t : ℂ)‖ - (Real.log R - Real.log ε)
          = Real.log ε - Real.log ‖z - (t : ℂ)‖ from by ring,
      abs_of_nonneg hnn, abs_of_nonpos hlog_nonpos,
      Real.log_div (ne_of_gt hposabs) (ne_of_gt hε)]
    linarith
  · have hge : ε ≤ ‖z - (t : ℂ)‖ := not_lt.mp hlt
    rw [max_eq_left hge, sub_self, abs_zero]
    exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) t

/-- **Truncation error bound.**  Replacing the log-kernel by its truncation at level `ε`
changes the potential by at most `2 ε`, uniformly in `z`. -/
theorem logPot_sub_truncPot_abs_le {B : Set ℝ} (hB : Bornology.IsBounded B) {R : ℝ}
    (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    |Work.TMComp.RC.logPot B R z - truncPot B R ε z| ≤ 2 * ε := by
  haveI : IsFiniteMeasure (volume.restrict B) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hB.measure_lt_top)
  set f : ℝ → ℝ := fun t => Real.log (R / ‖z - (t : ℂ)‖) with hfdef
  set g : ℝ → ℝ := fun t => Real.log (R / max ‖z - (t : ℂ)‖ ε) with hgdef
  set ψ : ℝ → ℝ := fun t => |Real.log (|t - z.re| / ε)| with hψdef
  set J : Set ℝ := Set.Ioc (z.re - ε) (z.re + ε) with hJdef
  have hf_int : Integrable f (volume.restrict B) := by
    rw [hfdef]; exact rcLogKernelIntegrable hB R z
  have hg_int : Integrable g (volume.restrict B) := by
    rw [hgdef]
    refine (hf_int.abs.add (integrable_const (|Real.log (R / ε)|))).mono' ?_ ?_
    · exact (continuous_truncKernel hR hε z).aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_eq_abs]
      by_cases hlt : ‖z - (t : ℂ)‖ < ε
      · rw [max_eq_right hlt.le]
        show |Real.log (R / ε)| ≤ |f t| + |Real.log (R / ε)|
        linarith [abs_nonneg (f t)]
      · rw [max_eq_left (not_lt.mp hlt)]
        show |f t| ≤ |f t| + |Real.log (R / ε)|
        linarith [abs_nonneg (Real.log (R / ε))]
  have hJmeas : MeasurableSet J := by rw [hJdef]; exact measurableSet_Ioc
  have hΦ_int_vol : Integrable (fun t => J.indicator ψ t) volume := by
    rw [integrable_indicator_iff hJmeas]
    simpa only [hψdef, hJdef] using (rcLogKernelIntegralOn z.re ε hε).1
  have hΦ_int_B : Integrable (fun t => J.indicator ψ t) (volume.restrict B) :=
    Integrable.mono_measure hΦ_int_vol Measure.restrict_le_self
  have hle : (fun t => |f t - g t|) ≤ᵐ[volume.restrict B] (fun t => J.indicator ψ t) := by
    filter_upwards [ae_ne_restrict B z.re] with t ht
    rw [hfdef, hgdef, hψdef, hJdef]
    exact abs_logKernel_sub_truncKernel_le hR hε z ht
  have hfg_int : Integrable (fun t => |f t - g t|) (volume.restrict B) :=
    (hf_int.sub hg_int).abs
  have hstep1 : ∫ t in B, |f t - g t| ≤ ∫ t in B, J.indicator ψ t :=
    integral_mono_ae hfg_int hΦ_int_B hle
  have hstep2 : ∫ t in B, J.indicator ψ t ≤ ∫ t, J.indicator ψ t :=
    setIntegral_le_integral hΦ_int_vol
      (Eventually.of_forall (fun t => Set.indicator_nonneg (fun _ _ => abs_nonneg _) t))
  have hstep3 : ∫ t, J.indicator ψ t = ∫ t in J, ψ t := integral_indicator hJmeas
  have hstep4 : ∫ t in J, ψ t = 2 * ε := by
    rw [hJdef, hψdef]; exact (rcLogKernelIntegralOn z.re ε hε).2
  have hbound : ∫ t in B, |f t - g t| ≤ 2 * ε := by
    rw [← hstep4]
    exact le_trans hstep1 (le_trans hstep2 hstep3.le)
  have hsub : (∫ t in B, f t) - (∫ t in B, g t) = ∫ t in B, (f t - g t) :=
    (integral_sub hf_int hg_int).symm
  have hL : Work.TMComp.RC.logPot B R z = ∫ t in B, f t := by
    simp only [Work.TMComp.RC.logPot, hfdef]
  have hR : truncPot B R ε z = ∫ t in B, g t := by
    simp only [truncPot, hgdef]
  calc |Work.TMComp.RC.logPot B R z - truncPot B R ε z|
      = |∫ t in B, (f t - g t)| := by
        rw [hL, hR, hsub]
    _ ≤ ∫ t in B, |f t - g t| := abs_integral_le_integral_abs
    _ ≤ 2 * ε := hbound

/-- Continuity of the logarithmic potential for a positive scale `R`. -/
theorem continuous_logPot_of_pos {B : Set ℝ} (hB : Bornology.IsBounded B) {R : ℝ} (hR : 0 < R) :
    Continuous (fun z : ℂ => Work.TMComp.RC.logPot B R z) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  show Tendsto (fun z : ℂ => Work.TMComp.RC.logPot B R z) (𝓝 z₀)
    (𝓝 (Work.TMComp.RC.logPot B R z₀))
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη8 : 0 < η / 8 := by linarith
  have hcont : Tendsto (fun z : ℂ => truncPot B R (η / 8) z) (𝓝 z₀)
      (𝓝 (truncPot B R (η / 8) z₀)) := by
    have h := rcTruncContinuous hB hR hη8
    exact h.continuousAt
  rw [Metric.tendsto_nhds] at hcont
  filter_upwards [hcont (η / 2) (by linarith)] with z hz
  rw [Real.dist_eq] at hz
  rw [Real.dist_eq]
  have h1 : |Work.TMComp.RC.logPot B R z - truncPot B R (η / 8) z| ≤ 2 * (η / 8) :=
    logPot_sub_truncPot_abs_le hB hR hη8 z
  have h2 : |Work.TMComp.RC.logPot B R z₀ - truncPot B R (η / 8) z₀| ≤ 2 * (η / 8) :=
    logPot_sub_truncPot_abs_le hB hR hη8 z₀
  have h3 : |truncPot B R (η / 8) z₀ - Work.TMComp.RC.logPot B R z₀| ≤ 2 * (η / 8) := by
    rw [abs_sub_comm]; exact h2
  have htri1 := abs_sub_le (Work.TMComp.RC.logPot B R z) (truncPot B R (η / 8) z)
    (Work.TMComp.RC.logPot B R z₀)
  have htri2 := abs_sub_le (truncPot B R (η / 8) z) (truncPot B R (η / 8) z₀)
    (Work.TMComp.RC.logPot B R z₀)
  linarith

theorem rcPot_continuous {B : Set ℝ} (hB : Bornology.IsBounded B) (R : ℝ) :
    Continuous (fun z : ℂ => Work.TMComp.RC.logPot B R z) := by
  rcases eq_or_ne R 0 with hR0 | hR0
  · subst hR0
    have h : (fun z : ℂ => Work.TMComp.RC.logPot B 0 z) = fun _ => (0 : ℝ) := by
      funext z
      simp [Work.TMComp.RC.logPot]
    rw [h]
    exact continuous_const
  · have hR : 0 < |R| := abs_pos.mpr hR0
    have hred : (fun z : ℂ => Work.TMComp.RC.logPot B R z)
        = (fun z : ℂ => Work.TMComp.RC.logPot B |R| z) := by
      funext z
      change (∫ t in B, Real.log (R / ‖z - (t : ℂ)‖))
          = ∫ t in B, Real.log (|R| / ‖z - (t : ℂ)‖)
      apply integral_congr_ae
      filter_upwards with t
      have hx : (0 : ℝ) ≤ ‖z - (t : ℂ)‖ := norm_nonneg _
      have h1 : |R| / ‖z - (t : ℂ)‖ = |R / ‖z - (t : ℂ)‖| := by
        rw [abs_div, abs_of_nonneg hx]
      rw [h1, Real.log_abs]
    rw [hred]
    exact continuous_logPot_of_pos hB hR

end Work.TMComp.RealCartan
