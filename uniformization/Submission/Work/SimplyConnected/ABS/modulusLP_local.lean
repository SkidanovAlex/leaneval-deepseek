import Mathlib
import Submission.Work.Modulus.Defs
import Submission.Work.Modulus.puncturedHarmonic
import Submission.Work.Modulus.localPoleExpansion
import Submission.Work.Modulus.chartPoleBound
import Submission.Work.Modulus.localHolomorphicModulus
import Submission.Work.Modulus.simpleZeroOfGrowth
import Submission.Work.Modulus.poleOrderModulus
import Submission.Work.Potential.removable_singularity_bounded_harmonic
import Submission.Work.SimplyConnected.ABS.Defs

/-!
# The local chapter of the holomorphic modulus, without decay

The chapter `Work.Modulus` constructs the holomorphic modulus `Φ = exp (-(E + iE*))` of a
*unit-pole Green function* `E` (`Work.UnitGreen.IsUnitGreenFunctionAt`), i.e. of a function which is
positive and harmonic off the pole, has a unit logarithmic pole there, **and whose superlevel sets
have compact closure** (decay at the ideal boundary).  The compactness conjunct is never used in the
chapter: every proof goes through

* the *harmonicity* of `E` off the pole, and
* the *logarithmic pole bound* at the pole.

This file re-proves the local part of the chapter with only those two hypotheses, so that the
decay-free Perron envelope `E := sweep (greenBarrier x₀ ρ) (univ \ {x₀})` of
`Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating'` can serve as the input.  Nothing
new is proved: each statement is the corresponding statement of `Work.Modulus` with the hypothesis
`Work.UnitGreen.IsUnitGreenFunctionAt z₀ E` replaced by

* `hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})`, and
* `hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E`

(the latter is the same logarithmic bound as the unit-pole conjunct of `IsUnitGreenFunctionAt`).
-/

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Filter Set
open Classical

namespace Work.ModulusLP

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **`E` is harmonic on the punctured surface** (decay-free form): the transport of
`hEharm : HarmonicOnX E (univ \ {z₀})` from `X` to the open subset `puncturedOpens z₀`. -/
theorem puncturedHarmonic {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) :
    Submission.HarmonicOnX (fun u : (Work.Modulus.puncturedOpens z₀) => E u.1) Set.univ := by
  intro u _
  change InnerProductSpace.HarmonicAt
    ((fun u : Work.Modulus.puncturedOpens z₀ => E u.1) ∘ (chartAt ℂ u).symm) ((chartAt ℂ u) u)
  have hxne : (u : X) ≠ z₀ := u.2
  have hEat : InnerProductSpace.HarmonicAt (E ∘ (chartAt ℂ (u : X)).symm)
      ((chartAt ℂ (u : X)) (u : X)) :=
    hEharm (u : X) ⟨mem_univ _, by simpa using hxne⟩
  have heq : ((fun u : Work.Modulus.puncturedOpens z₀ => E u.1) ∘ (chartAt ℂ u).symm)
      =ᶠ[𝓝 ((chartAt ℂ (u : X)) (u : X))] (E ∘ (chartAt ℂ (u : X)).symm) := by
    filter_upwards [(chartAt ℂ u).open_target.mem_nhds
      (Work.Modulus.opensChartAt_mem_target _ u)] with z hz
    simp only [Function.comp_apply]
    rw [Work.Modulus.opensChartAt_symm_eqOn _ u hz]
  rw [Work.Modulus.opensChartAt_apply (Work.Modulus.puncturedOpens z₀) u]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hEat

/-- **The local expansion of `E` at its pole** (decay-free form): in the preferred chart at `z₀`,
`E x = -log ‖c x - c z₀‖ + H (c x)` for a harmonic `H` on a ball around `c z₀`.  Only harmonicity
and the logarithmic pole bound are used. -/
theorem localPoleExpansion {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ z₀) z₀) ρ) ∧
      (∀ x ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, x ≠ z₀ →
        E x = -Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ + H ((chartAt ℂ z₀) x)) := by
  have hharm : Submission.HarmonicOnX E (univ \ {z₀}) := hEharm
  obtain ⟨C, V, hVnhds, hVbnd⟩ := hpole
  have hsrc : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hsymm₀ : (chartAt ℂ z₀).symm ((chartAt ℂ z₀) z₀) = z₀ := (chartAt ℂ z₀).left_inv hsrc
  have htgt₀ : (chartAt ℂ z₀) z₀ ∈ (chartAt ℂ z₀).target := (chartAt ℂ z₀).map_source hsrc
  have hW : V ∩ (chartAt ℂ z₀).source ∈ 𝓝 z₀ :=
    inter_mem hVnhds ((chartAt ℂ z₀).open_source.mem_nhds hsrc)
  have hpre : (chartAt ℂ z₀).symm ⁻¹' (V ∩ (chartAt ℂ z₀).source) ∈ 𝓝 ((chartAt ℂ z₀) z₀) :=
    ContinuousAt.preimage_mem_nhds
      ((chartAt ℂ z₀).continuousAt_symm htgt₀) (by simpa [hsymm₀] using hW)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z₀).open_target.mem_nhds htgt₀)
  set R : ℝ := min ε δ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact lt_min hε hδ
  have hRε : Metric.ball ((chartAt ℂ z₀) z₀) R ⊆ (chartAt ℂ z₀).symm ⁻¹'
      (V ∩ (chartAt ℂ z₀).source) := by
    rw [hRdef]; exact (Metric.ball_subset_ball (min_le_left ε δ)).trans hεsub
  have hRδ : Metric.ball ((chartAt ℂ z₀) z₀) R ⊆ (chartAt ℂ z₀).target := by
    rw [hRdef]; exact (Metric.ball_subset_ball (min_le_right ε δ)).trans hδsub
  obtain ⟨H, hHharm, hHeq⟩ := Work.Potential.removable_singularity_ball_center
    (u := fun ξ : ℂ => E ((chartAt ℂ z₀).symm ξ) + Real.log ‖ξ - (chartAt ℂ z₀) z₀‖)
    (a := (chartAt ℂ z₀) z₀) (R := R) (M := C) hRpos
    (fun z hz hzne => by
      have hzR : z ∈ Metric.ball ((chartAt ℂ z₀) z₀) R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hz
      have hzpre : (chartAt ℂ z₀).symm z ∈ V ∩ (chartAt ℂ z₀).source := hRε hzR
      have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm z) = z :=
        (chartAt ℂ z₀).right_inv (hRδ hzR)
      have hyne : (chartAt ℂ z₀).symm z ≠ z₀ := fun hcon => hzne (by rw [← hcs, hcon])
      have hEharm' : InnerProductSpace.HarmonicAt (E ∘ (chartAt ℂ z₀).symm) z := by
        have h1 : Submission.HarmonicOnXAt E ((chartAt ℂ z₀).symm z) :=
          hharm _ ⟨mem_univ _, hyne⟩
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := E)
          (x := (chartAt ℂ z₀).symm z) (y := z₀) hzpre.2).mp h1
        rwa [hcs] at h2
      have hlogharm : InnerProductSpace.HarmonicAt
          (fun ξ : ℂ => Real.log ‖ξ - (chartAt ℂ z₀) z₀‖) z :=
        AnalyticAt.harmonicAt_log_norm (f := fun ξ : ℂ => ξ - (chartAt ℂ z₀) z₀)
          (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)
      exact hEharm'.add hlogharm)
    (fun z hz hzne => by
      have hzR : z ∈ Metric.ball ((chartAt ℂ z₀) z₀) R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hz
      have hzpre : (chartAt ℂ z₀).symm z ∈ V ∩ (chartAt ℂ z₀).source := hRε hzR
      have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm z) = z :=
        (chartAt ℂ z₀).right_inv (hRδ hzR)
      have hyne : (chartAt ℂ z₀).symm z ≠ z₀ := fun hcon => hzne (by rw [← hcs, hcon])
      have h1 := hVbnd ((chartAt ℂ z₀).symm z) hzpre.1 ⟨mem_univ _, hyne⟩ hyne
      rw [hcs] at h1
      exact h1)
  refine ⟨R / 2, by linarith, H, ?_, ?_⟩
  · intro z hz
    exact hHharm z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  · intro x hx hxne
    rw [Submission.mem_chartBall] at hx
    obtain ⟨hxsrc, hxball⟩ := hx
    have hcxne : (chartAt ℂ z₀) x ≠ (chartAt ℂ z₀) z₀ :=
      fun hcon => hxne ((chartAt ℂ z₀).injOn hxsrc hsrc hcon)
    have hlt : ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ < R / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    have hval := hHeq ((chartAt ℂ z₀) x) hlt hcxne
    rw [(chartAt ℂ z₀).left_inv hxsrc] at hval
    linarith

/-- **The pole bound in the preferred chart** (decay-free form). -/
theorem chartPoleBound {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball ((chartAt ℂ z₀) z₀) ε ⊆ (chartAt ℂ z₀).target ∧
      ∃ C : ℝ, ∀ w ∈ Metric.ball ((chartAt ℂ z₀) z₀) ε, w ≠ (chartAt ℂ z₀) z₀ →
        (chartAt ℂ z₀).symm w ≠ z₀ ∧
        |E ((chartAt ℂ z₀).symm w) + Real.log ‖w - (chartAt ℂ z₀) z₀‖| ≤ C := by
  obtain ⟨ρ, hρ, H, hH, hexp⟩ := localPoleExpansion hEharm hpole
  set a : ℂ := (chartAt ℂ z₀) z₀ with ha
  have hatgt : a ∈ (chartAt ℂ z₀).target := by
    rw [ha]
    exact (chartAt ℂ z₀).map_source (mem_chart_source ℂ z₀)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z₀).open_target.mem_nhds hatgt)
  set r : ℝ := min (ρ / 2) (δ / 2) with hr
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hbdd : ∃ C : ℝ, ∀ w ∈ Metric.closedBall a r, |H w| ≤ C := by
    have hcont : ContinuousOn H (Metric.closedBall a r) :=
      hH.continuousOn.mono (Metric.closedBall_subset_ball hrρ)
    obtain ⟨C, hC⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hcont
    exact ⟨C, fun w hw => by rw [← Real.norm_eq_abs]; exact hC w hw⟩
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨r, hrpos, ?_, C, ?_⟩
  · exact (Metric.ball_subset_ball hrδ.le).trans hδsub
  · intro w hw hwne
    have hwt : w ∈ (chartAt ℂ z₀).target := hδsub (Metric.ball_subset_ball hrδ.le hw)
    have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm w) = w := (chartAt ℂ z₀).right_inv hwt
    have hsne : (chartAt ℂ z₀).symm w ≠ z₀ := by
      intro hcon
      exact hwne (by rw [← hcs, hcon, ha])
    refine ⟨hsne, ?_⟩
    have hmem : (chartAt ℂ z₀).symm w ∈ Submission.chartBall (chartAt ℂ z₀) a ρ := by
      refine ⟨OpenPartialHomeomorph.map_target _ hwt, ?_⟩
      change (chartAt ℂ z₀) ((chartAt ℂ z₀).symm w) ∈ Metric.ball a ρ
      rw [hcs]
      exact Metric.ball_subset_ball hrρ.le hw
    have hval := hexp ((chartAt ℂ z₀).symm w) hmem hsne
    rw [hval, hcs]
    have harith : -(Real.log ‖w - a‖) + H w + Real.log ‖w - a‖ = H w := by ring
    rw [harith]
    exact hC w (Metric.ball_subset_closedBall hw)

/-- **The local holomorphic modulus** (decay-free form). -/
theorem localHolomorphicModulus_of_unitGreen {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    ∃ (ρ : ℝ) (Φ : X → ℂ), 0 < ρ ∧
      Submission.HolomorphicOnX Φ (Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ) ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      (∀ x ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, x ≠ z₀ →
        ‖Φ x‖ = Real.exp (-(E x))) := by
  obtain ⟨ρ₀, hρ₀, H, hHharm, hexp⟩ := localPoleExpansion hEharm hpole
  obtain ⟨F, hFana, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := H) hHharm
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hsrc : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have hatgt : a ∈ c.target := c.map_source hsrc
  have ha_ball : a ∈ Metric.ball a ρ₀ := by simp [Metric.mem_ball, hρ₀]
  set Φ : X → ℂ := fun x => (c x - a) * Complex.exp (-(F (c x))) with hΦ
  refine ⟨ρ₀ / 2, Φ, by linarith, ?_, ?_, ?_⟩
  · intro x hx
    have hxsrc : x ∈ c.source := hx.1
    have hxball : c x ∈ Metric.ball a ρ₀ :=
      Metric.ball_subset_ball (by linarith) hx.2
    refine (Submission.HolomorphicOnXAt_iff_chart (f := Φ) (x := x) (y := z₀) hxsrc).mpr ?_
    have hev : (Φ ∘ c.symm) =ᶠ[𝓝 (c x)]
        (fun w : ℂ => (w - a) * Complex.exp (-(F w))) := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hxsrc),
        Metric.isOpen_ball.mem_nhds hxball] with w hwt _hwb
      simp only [Function.comp_apply, hΦ]
      rw [c.right_inv hwt]
    refine (AnalyticAt.mul (analyticAt_id.sub analyticAt_const)
      (((hFana (c x) hxball).neg).cexp)).congr hev.symm
  · refine ⟨fun w : ℂ => Complex.exp (-(F w)), ?_, Complex.exp_ne_zero _, ?_⟩
    · exact ((hFana a ha_ball).neg).cexp
    · have hev : (Φ ∘ c.symm) =ᶠ[𝓝 a]
          (fun w : ℂ => (w - a) * Complex.exp (-(F w))) := by
        filter_upwards [c.open_target.mem_nhds hatgt, Metric.isOpen_ball.mem_nhds ha_ball]
          with w hwt _hwb
        simp only [Function.comp_apply, hΦ]
        rw [c.right_inv hwt]
      exact hev
  · intro x hx hxne
    have hxsrc : x ∈ c.source := hx.1
    have hxball : c x ∈ Metric.ball a ρ₀ := Metric.ball_subset_ball (by linarith) hx.2
    have hcxne : c x ≠ a := fun h => hxne (c.injOn hxsrc hsrc h)
    have hfre : (F (c x)).re = H (c x) := hFre hxball
    have hnorm : ‖Φ x‖ = ‖c x - a‖ * Real.exp (-(H (c x))) := by
      simp only [hΦ, norm_mul, Complex.norm_exp, Complex.neg_re, hfre]
    rw [hnorm, hexp x ⟨hxsrc, hxball⟩ hxne]
    have hlog : Real.exp (Real.log ‖c x - a‖) = ‖c x - a‖ :=
      Real.exp_log (norm_pos_iff.mpr (sub_ne_zero.mpr hcxne))
    have harith : -( -Real.log ‖c x - a‖ + H (c x))
        = Real.log ‖c x - a‖ + (-(H (c x))) := by ring
    rw [harith, Real.exp_add, hlog]

/-- **The zero at the pole is simple** (decay-free form). -/
theorem poleOrderModulus_of_unitGreen {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    {Φ : X → ℂ} (hhol : Submission.HolomorphicOnX Φ Set.univ)
    (hne : ∀ x, x ≠ z₀ → Φ x ≠ 0)
    (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) :
    Submission.HasLogPoleAt z₀ Φ := by
  obtain ⟨ε, hε, _hballtgt, C, hC⟩ := chartPoleBound hEharm hpole
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hg : AnalyticAt ℂ (Φ ∘ c.symm) a := hhol z₀ (mem_univ z₀)
  have hup : ∀ w ∈ Metric.ball a ε, w ≠ a → ‖(Φ ∘ c.symm) w‖ ≤ Real.exp C * ‖w - a‖ := by
    intro w hw hwne
    obtain ⟨hxne, hbnd⟩ := hC w hw hwne
    have hr : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have h := (Work.Modulus.exp_bounds_of_abs_add_log hr hbnd).1
    simpa [hmod (c.symm w) hxne] using h
  have hlo : ∀ w ∈ Metric.ball a ε, w ≠ a → Real.exp (-C) * ‖w - a‖ ≤ ‖(Φ ∘ c.symm) w‖ := by
    intro w hw hwne
    obtain ⟨hxne, hbnd⟩ := hC w hw hwne
    have hr : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have h := (Work.Modulus.exp_bounds_of_abs_add_log hr hbnd).2
    simpa [hmod (c.symm w) hxne] using h
  obtain ⟨F, hFana, hFne, hFeq⟩ :=
    Work.Modulus.simpleZeroOfGrowth hε (Real.exp_pos (-C)) hg hup hlo
  refine ⟨F, ?_, ?_, ?_⟩
  · rwa [← ha]
  · rwa [← ha]
  · rw [← ha]
    exact hFeq

end Work.ModulusLP
