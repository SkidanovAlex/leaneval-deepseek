import ChallengeDeps
import Submission.Balayage
import Submission.GreenFunction

/-!
# Frontier points of the chart annulus and the two-constants estimate

This module contains the last ingredient of the classical *two-constants* (harmonic measure)
estimate for the hitting probability: the fact that a point of the inner sphere is a frontier
point of the chart annulus `chartBall c a ρ₂ \ chartClosedBall c a ρ`, which supplies the
non-emptiness of the frontier required by the maximum principle
`Submission.SubharmonicOnX.le_of_frontier_limsup`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A point of the inner sphere `‖c· - a‖ = ρ` is in the closure of the annulus
`chartBall c a ρ₂ \ chartClosedBall c a ρ`: it is the limit of the curve
`t ↦ c.symm (c ξ + t·u)`, `u := (c ξ - a)/ρ`, which lies in the annulus for `0 < t < ρ₂ - ρ`. -/
theorem chartSphere_subset_closure_diff {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ ρ₂ : ℝ}
    (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂) (hsub : Metric.closedBall a ρ₂ ⊆ c.target) :
    chartSphere c a ρ ⊆ closure (chartBall c a ρ₂ \ chartClosedBall c a ρ) := by
  intro ξ hξ
  obtain ⟨hξsrc, hξsph⟩ := mem_chartSphere.mp hξ
  have hξnorm : ‖c ξ - a‖ = ρ := by
    rw [Metric.mem_sphere, dist_eq_norm] at hξsph
    exact hξsph
  rw [mem_closure_iff_nhds]
  intro o ho
  have himg : c '' (o ∩ c.source) ∈ 𝓝 (c ξ) :=
    c.image_mem_nhds hξsrc (Filter.inter_mem ho (c.open_source.mem_nhds hξsrc))
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.mp himg
  set ε : ℝ := min (ε₀ / 2) ((ρ₂ - ρ) / 2) with hεdef
  have hεpos : 0 < ε := lt_min (half_pos hε₀) (half_pos (by linarith))
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
  have hερ : ε < ρ₂ - ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self (by linarith))
  have hρne : (ρ : ℂ) ≠ 0 := by simpa using hρ.ne'
  set u : ℂ := (c ξ - a) / (ρ : ℂ) with hu
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_div, hξnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      div_self hρ.ne']
  set w : ℂ := c ξ + (ε : ℂ) * u with hwdef
  have hwball : w ∈ Metric.ball (c ξ) ε₀ := by
    rw [Metric.mem_ball, dist_eq_norm, hwdef, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hεpos, hunorm, mul_one]
    exact hεε₀
  have hwnorm : ‖w - a‖ = ρ + ε := by
    have hkey : w - a = ((1 + ε / ρ : ℝ) : ℂ) * (c ξ - a) := by
      rw [hwdef, hu]; push_cast; field_simp; ring
    rw [hkey, norm_mul, hξnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 + ε / ρ)]
    field_simp
  obtain ⟨z, hz, hzc⟩ := hε₀sub hwball
  have hzball : c z ∈ Metric.ball a ρ₂ := by
    rw [Metric.mem_ball, dist_eq_norm, hzc, hwnorm]
    linarith
  refine ⟨z, hz.1, ⟨hz.2, hzball⟩, ?_⟩
  rw [mem_chartClosedBall]
  rintro ⟨-, hzcl⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hzcl
  rw [hzc, hwnorm] at hzcl
  linarith

/-- A point of the inner sphere is a frontier point of the annulus. -/
theorem chartSphere_subset_frontier_diff {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ ρ₂ : ℝ}
    (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂) (hsub : Metric.closedBall a ρ₂ ⊆ c.target) :
    chartSphere c a ρ ⊆ frontier (chartBall c a ρ₂ \ chartClosedBall c a ρ) := by
  intro ξ hξ
  rw [← closure_sdiff_interior]
  refine ⟨chartSphere_subset_closure_diff hρ hρρ₂ hsub hξ, ?_⟩
  intro hint
  have hsubc : (chartBall c a ρ₂ \ chartClosedBall c a ρ) ⊆ (chartBall c a ρ)ᶜ := by
    intro z hz hz'
    exact hz.2 (chartBall_subset_chartClosedBall c a ρ hz')
  have hint' : ξ ∈ interior ((chartBall c a ρ)ᶜ) := interior_mono hsubc hint
  rw [interior_compl] at hint'
  apply hint'
  obtain ⟨hsrc, hsph⟩ := mem_chartSphere.mp hξ
  have hsubρ : Metric.closedBall a ρ ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hρρ₂.le).trans hsub
  refine chartClosedBall_subset_closure_chartBall hρ hsubρ ?_
  rw [mem_chartClosedBall, Metric.mem_closedBall, dist_eq_norm]
  rw [Metric.mem_sphere, dist_eq_norm] at hsph
  exact ⟨hsrc, hsph.le⟩

/-- The frontier of the chart annulus is non-empty. -/
theorem frontier_diff_nonempty {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ ρ₂ : ℝ}
    (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂) (hsub : Metric.closedBall a ρ₂ ⊆ c.target) :
    (frontier (chartBall c a ρ₂ \ chartClosedBall c a ρ)).Nonempty := by
  have hmem : a + (ρ : ℂ) ∈ Metric.closedBall a ρ₂ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    linarith
  refine ⟨c.symm (a + (ρ : ℂ)), chartSphere_subset_frontier_diff hρ hρρ₂ hsub ?_⟩
  rw [mem_chartSphere]
  refine ⟨c.map_target (hsub hmem), ?_⟩
  rw [c.right_inv (hsub hmem), Metric.mem_sphere, dist_eq_norm]
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]

/-! ## The two-constants (harmonic measure) estimate -/

/-- **Two-constants estimate for the hitting probability.**  For `0 < ρ < ρ₂` with the closed
chart disc of radius `ρ₂` inside the chart target, the hitting probability of the chart disc of
radius `ρ` dominates the harmonic measure of that disc in the chart ball of radius `ρ₂`:
`Real.log (ρ₂ / ‖c x - c z₀‖) / Real.log (ρ₂ / ρ) ≤ hittingProbability c (c z₀) ρ x` for every
`x` with `ρ < ‖c x - c z₀‖ < ρ₂`. -/
theorem hittingProbability_ge_log_ratio {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    ∀ x ∈ chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂,
      x ∉ chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ →
      Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) / Real.log (ρ₂ / ρ) ≤
        hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x := by
  intro x hx hx'
  have hρ₂ : 0 < ρ₂ := lt_trans hρ hρρ₂
  have hsubρ : Metric.closedBall (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).target :=
    (Metric.closedBall_subset_closedBall hρρ₂.le).trans hsub
  have hdenpos : 0 < Real.log (ρ₂ / ρ) := Real.log_pos (by rw [one_lt_div hρ]; exact hρρ₂)
  have hlogeq : Real.log ρ₂ - Real.log ρ = Real.log (ρ₂ / ρ) :=
    (Real.log_div hρ₂.ne' hρ.ne').symm
  have hkey : ∀ v ∈ hittingFamily (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ,
      v x + Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) / Real.log (ρ₂ / ρ) ≤ 0 := by
    intro v hv
    -- the barrier
    have hMharm : ∀ z ∈ chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
        chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ,
        HarmonicOnXAt (fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
          (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) z := by
      intro z hz
      have hzsrc : z ∈ (chartAt ℂ z₀).source := chartBall_subset_source _ _ _ hz.1
      have hzne : chartAt ℂ z₀ z ≠ chartAt ℂ z₀ z₀ := by
        intro h
        have hnorm : ‖chartAt ℂ z₀ z - chartAt ℂ z₀ z₀‖ = 0 := by rw [h, sub_self, norm_zero]
        refine hz.2 ⟨hzsrc, ?_⟩
        rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, hnorm]
        exact hρ.le
      exact ((harmonicOnXAt_const (Real.log ρ₂)).sub
        (harmonicOnXAt_log_norm_chartAt (z₀ := z₀) hzsrc hzne)).const_smul _
    -- continuity of the barrier on the annulus
    have hMcont : ContinuousOn (fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
        (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖))
        (chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
          chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) := by
      have hsrc : chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
          chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).source :=
        (Set.diff_subset).trans (chartBall_subset_source _ _ _)
      have hnk : ContinuousOn
          (fun y : X => ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) _ :=
        continuous_norm.comp_continuousOn
          (((chartAt ℂ z₀).continuousOn.sub continuousOn_const).mono hsrc)
      have hlog : ContinuousOn
          (fun y : X => Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) _ :=
        hnk.log (fun y hy => by
          have hyne : chartAt ℂ z₀ y ≠ chartAt ℂ z₀ z₀ := by
            intro h
            have hnorm : ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖ = 0 := by rw [h, sub_self, norm_zero]
            refine hy.2 ⟨hsrc hy, ?_⟩
            rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, hnorm]
            exact hρ.le
          simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyne)])
      exact continuousOn_const.mul (continuousOn_const.sub hlog)
    -- the barrier is continuous at the frontier points
    have hlim : ∀ ξ ∈ frontier (chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
        chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ), ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in 𝓝[chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
          chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ] ξ,
          (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) z ≤ 0 + ε := by
      intro ξ hξfr ε hε
      have hcases := frontier_chartBall_diff_chartClosedBall_subset hρ hρρ₂ hsub hξfr
      rcases hcases with houter | hinner
      · obtain ⟨hsrc, hsph⟩ := mem_chartSphere.mp houter
        have hnorm : ‖chartAt ℂ z₀ ξ - chartAt ℂ z₀ z₀‖ = ρ₂ := by
          rw [Metric.mem_sphere, dist_eq_norm] at hsph; exact hsph
        have hMval : (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ ξ - chartAt ℂ z₀ z₀‖) = 0 := by
          rw [hnorm, sub_self, mul_zero]
        have hct : ContinuousAt (fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ := by
          have h1 : ContinuousAt (fun y : X => ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) ξ :=
            continuous_norm.continuousAt.comp
              (((chartAt ℂ z₀).continuousAt hsrc).sub continuousAt_const)
          have h2 : ContinuousAt (fun y : X =>
              Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) ξ :=
            h1.log (by rw [hnorm]; exact hρ₂.ne')
          exact ((continuousAt_const.sub h2).const_mul _)
        have hle0 : (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ ≤ 0 := by
          rw [Pi.add_apply, hMval, add_zero]
          exact hv.2.2 ξ
        have hlt : (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ < 0 + ε := by
          linarith [hle0, hε]
        have hctv : ContinuousAt (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ :=
          ((hv.1.1).continuousAt Filter.univ_mem).add hct
        have hev : ∀ᶠ z in 𝓝 ξ, (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) z < 0 + ε :=
          hctv.eventually (Iio_mem_nhds hlt)
        exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun z hz => hz.le)
      · obtain ⟨hsrc, hsph⟩ := mem_chartSphere.mp hinner
        have hnorm : ‖chartAt ℂ z₀ ξ - chartAt ℂ z₀ z₀‖ = ρ := by
          rw [Metric.mem_sphere, dist_eq_norm] at hsph; exact hsph
        have hMval : (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ ξ - chartAt ℂ z₀ z₀‖) = 1 := by
          rw [hnorm, hlogeq]
          exact inv_mul_cancel₀ hdenpos.ne'
        have hct : ContinuousAt (fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ := by
          have h1 : ContinuousAt (fun y : X => ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) ξ :=
            continuous_norm.continuousAt.comp
              (((chartAt ℂ z₀).continuousAt hsrc).sub continuousAt_const)
          have h2 : ContinuousAt (fun y : X =>
              Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) ξ :=
            h1.log (by rw [hnorm]; exact hρ.ne')
          exact ((continuousAt_const.sub h2).const_mul _)
        have hξcl : ξ ∈ chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ := by
          refine ⟨hsrc, ?_⟩
          rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, hnorm]
        have hξle : v ξ ≤ -1 := hittingFamily_le_neg_one_of_mem_chartClosedBall hρ hsubρ hv hξcl
        have hle0 : (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ ≤ 0 := by
          rw [Pi.add_apply, hMval]
          linarith
        have hlt : (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ < 0 + ε := by
          linarith [hle0, hε]
        have hctv : ContinuousAt (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ :=
          ((hv.1.1).continuousAt Filter.univ_mem).add hct
        have hev : ∀ᶠ z in 𝓝 ξ, (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
            (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) z < 0 + ε :=
          hctv.eventually (Iio_mem_nhds hlt)
        exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun z hz => hz.le)
    -- the maximum principle on the annulus
    have hsub_w : SubharmonicOnX (v + fun y : X => (Real.log (ρ₂ / ρ))⁻¹ *
        (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖))
        (chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
          chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) := by
      refine ⟨(hv.1.1.mono (Set.subset_univ _)).add hMcont, fun z hz => ?_⟩
      exact (hv.1.2 z (mem_univ z)).add_harmonicOnXAt (hMharm z hz)
    have hUopen : IsOpen (chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
        chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) :=
      (chartBall_isOpen _ _ _).sdiff (isClosed_chartClosedBall hsubρ)
    have hcomp : IsCompact (closure (chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
        chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ)) :=
      (isCompact_chartClosedBall hsub).of_isClosed_subset isClosed_closure
        (closure_minimal (Set.diff_subset.trans (chartBall_subset_chartClosedBall _ _ _))
          (isClosed_chartClosedBall hsub))
    have hne := frontier_diff_nonempty (c := chartAt ℂ z₀) (a := chartAt ℂ z₀ z₀) hρ hρρ₂ hsub
    have hle := SubharmonicOnX.le_of_frontier_limsup (a := 0) hUopen hsub_w hcomp hne hlim
    have hxU : x ∈ chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
        chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ := ⟨hx, hx'⟩
    have hfin := hle x hxU
    rw [Pi.add_apply] at hfin
    -- convert the barrier back to the divided logarithm
    have hxne : chartAt ℂ z₀ x ≠ chartAt ℂ z₀ z₀ := by
      intro h
      have hnorm : ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖ = 0 := by rw [h, sub_self, norm_zero]
      refine hx' ⟨chartBall_subset_source _ _ _ hx, ?_⟩
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, hnorm]
      exact hρ.le
    have hdiv : (Real.log (ρ₂ / ρ))⁻¹ *
        (Real.log ρ₂ - Real.log ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖)
        = Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) / Real.log (ρ₂ / ρ) := by
      rw [Real.log_div hρ₂.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxne)),
        div_eq_mul_inv]
      ring
    rw [hdiv] at hfin
    linarith
  -- conclude via the envelope
  have hbal : balayage (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x ≤
      -(Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) / Real.log (ρ₂ / ρ)) := by
    rw [balayage, upperEnvelope]
    refine csSup_le ((hittingFamily_nonempty (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ).image _) ?_
    rintro y ⟨v, hv, rfl⟩
    linarith [hkey v hv]
  rw [hittingProbability]
  linarith

/-- **Boundary regularity of the hitting probability at the inner sphere.**  As `x` approaches a
point of the inner sphere of the chart annulus, the hitting probability tends to `1` — the
classical Dirichlet regularity statement, which the two-constants estimate supplies. -/
theorem hittingProbability_tendsto_one_at_sphere {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ)
    (hρρ₂ : ρ < ρ₂) (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target) :
    ∀ ξ ∈ chartSphere (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x in 𝓝[chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂ \
        chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ] ξ,
        1 - ε ≤ hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x := by
  intro ξ hξ ε hε
  obtain ⟨hξsrc, hξsph⟩ := mem_chartSphere.mp hξ
  have hξnorm : ‖chartAt ℂ z₀ ξ - chartAt ℂ z₀ z₀‖ = ρ := by
    rw [Metric.mem_sphere, dist_eq_norm] at hξsph
    exact hξsph
  have hρ₂ : 0 < ρ₂ := lt_trans hρ hρρ₂
  have hdenpos : 0 < Real.log (ρ₂ / ρ) := Real.log_pos (by rw [one_lt_div hρ]; exact hρρ₂)
  have hctnum : ContinuousAt (fun y : X => Real.log (ρ₂ / ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖)) ξ := by
    have h1 : ContinuousAt (fun y : X => ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) ξ :=
      continuous_norm.continuousAt.comp
        (((chartAt ℂ z₀).continuousAt hξsrc).sub continuousAt_const)
    have h2 : ContinuousAt (fun y : X => ρ₂ / ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) ξ :=
      continuousAt_const.div h1 (by rw [hξnorm]; exact hρ.ne')
    exact h2.log (by rw [hξnorm]; positivity)
  have hct : ContinuousAt (fun y : X => Real.log (ρ₂ / ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) /
      Real.log (ρ₂ / ρ)) ξ := hctnum.div_const _
  have hval : (fun y : X => Real.log (ρ₂ / ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) /
      Real.log (ρ₂ / ρ)) ξ = 1 := by
    show Real.log (ρ₂ / ‖chartAt ℂ z₀ ξ - chartAt ℂ z₀ z₀‖) / Real.log (ρ₂ / ρ) = 1
    rw [hξnorm]
    exact div_self hdenpos.ne'
  have hlt : 1 - ε < (fun y : X => Real.log (ρ₂ / ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) /
      Real.log (ρ₂ / ρ)) ξ := by rw [hval]; linarith
  filter_upwards [(hct.eventually (lt_mem_nhds hlt)).filter_mono
    nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxmem
  exact hx.le.trans (hittingProbability_ge_log_ratio hρ hρρ₂ hsub x hxmem.1 hxmem.2)

/-- **Lower bound for the normalised hitting probability** (the Green-function lower bound in
finite form): for `ρ ≤ 1` and `x` in the chart annulus,
`log (ρ₂/‖c x - a‖) · ((-log ρ)/log (ρ₂/ρ)) ≤ (-log ρ) · hittingProbability c a ρ x`.
The factor `(-log ρ)/log (ρ₂/ρ)` tends to `1` as `ρ → 0`, so this is the finite-`ρ` form of
`liminf_{ρ→0} (-log ρ) h_ρ ≥ log (ρ₂/‖c x - a‖)`. -/
theorem hittingProbability_normalized_ge {z₀ : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hρρ₂ : ρ < ρ₂) (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ₂ ⊆ (chartAt ℂ z₀).target)
    {x : X} (hx : x ∈ chartBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ₂)
    (hx' : x ∉ chartClosedBall (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ) :
    Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) *
        ((-Real.log ρ) / Real.log (ρ₂ / ρ)) ≤
      (-Real.log ρ) * hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x := by
  have hlog_nonneg : 0 ≤ -Real.log ρ := by
    rw [neg_nonneg, ← Real.log_one]
    exact Real.log_le_log hρ hρ₁
  have hmain := hittingProbability_ge_log_ratio hρ hρρ₂ hsub x hx hx'
  have h2 := mul_le_mul_of_nonneg_left hmain hlog_nonneg
  calc Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) *
        ((-Real.log ρ) / Real.log (ρ₂ / ρ))
      = (-Real.log ρ) * (Real.log (ρ₂ / ‖chartAt ℂ z₀ x - chartAt ℂ z₀ z₀‖) /
          Real.log (ρ₂ / ρ)) := by ring
    _ ≤ (-Real.log ρ) * hittingProbability (chartAt ℂ z₀) (chartAt ℂ z₀ z₀) ρ x := h2

end Submission
