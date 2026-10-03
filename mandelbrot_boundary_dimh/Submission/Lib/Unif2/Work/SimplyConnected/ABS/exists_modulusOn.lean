import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusMain
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.coveringAux
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne
import Submission.Lib.Unif2.Work.Modulus.isCoveringMap_branchProj_of_localBranches
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_simpleZero_of_modulus_exp
import Submission.Lib.Unif2.Work.Potential.removable_singularity_bounded_harmonic

/-!
# The holomorphic modulus of the Green function of a simply connected domain

Hubbard, *Teichmüller theory* Vol. 1, Chapter 1; Anghel–Bruin–Stan,
*Uniformization of Riemann surfaces revisited*, arXiv:2008.12189, the disc lemma (item 10).

This module proves `Work.SimplyConnected.ABS.exists_modulusOn`: given a Green function `E` of an open
connected simply connected domain `Ω` of a Riemann surface `X`, with pole `x₀` — in the *satisfiable*
form of `Work.SimplyConnected.ABS.IsGreenOn`, i.e. positivity and harmonicity off the pole, a bounded
logarithmic pole at `x₀`, and superlevel sets relatively compact in `Ω` — there is a holomorphic
*modulus* `Φ` of `E` on `Ω`: `Φ` is holomorphic at every point of `Ω`, has a simple zero at `x₀` in
the preferred chart at `x₀`, and `‖Φ x‖ = exp (-(E x))` for `x ∈ Ω`, `x ≠ x₀`.

## Strategy

Everything happens on the open subspace `U := ⟨Ω, hΩo⟩` of `X`, which is a Riemann surface in its own
right (open subsets inherit the charted-space and manifold structures).  On `U`:

* `E` restricted to `U` is harmonic off its pole and has a bounded logarithmic pole there
  (`harmonicOnXAt_restrict`, `opensChartAt_apply_of_mem`), so every point of `U` has a chart ball
  carrying a *local branch* of the modulus `exp (-E)`: a holomorphic `Φ` which does not vanish off the
  pole, with `‖Φ y‖ = exp (-(E y))`, and whose pair (value, chart derivative) never vanishes on the
  ball (`exists_localBranch_chartBall_of_boundedPole`, built from
  `Work.Modulus.localPoleExpansion`'s argument — the removable singularity of a bounded harmonic
  function on a punctured disc — and from `Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt`
  off the pole);
* the bundle of local branches of the multivalued modulus `exp (-(E + iE*))` over `U`
  (`Work.SC.ModulusBundle`, whose points are the branches, encoded over the pole by the derivative) is
  therefore a covering space of `U` (`Work.Modulus.isCoveringMap_branchProj_of_localBranches`);
* `U` is simply connected by hypothesis, so the monodromy of that covering is trivial and the covering
  has a global section (`Work.SC.exists_holomorphic_modulus_of_isCoveringMap`): a single-valued
  holomorphic `Φ'` on `U` with `Φ' ≠ 0` off the pole and `‖Φ'‖ = exp (-E)` there.

The functions are then transported back to `X` (extended by `0` outside `Ω`): holomorphy is a local
statement (`holomorphicOnXAt_of_restrict_eqOn`), and at the pole the two-sided linear growth bound
`exp (-C) ‖w - z₀‖ ≤ |Φ| ≤ exp C ‖w - z₀‖`, read in the preferred chart at `x₀`, forces the zero to be
simple (`Work.SimplyConnected.ABS.exists_simpleZero_of_modulus_exp`, via
`Work.Modulus.simpleZeroOfGrowth`).

Note that the `Submission.HasGreenFunctionE` interface of the parallel `Work.Modulus` development is
*unsatisfiable* (its superlevel sets `{ε ≤ E}` are required to be compact, which fails in every
punctured neighbourhood of the pole); the local arguments of that development are therefore reused here
through hypotheses-only restatements (`localPoleExpansion_of_boundedPole`,
`localBranch_at_pole_of_boundedPole`) rather than through `HasGreenFunctionE`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Chart and harmonicity bookkeeping for open subspaces

The chart of an open subspace `U ⊆ X` at a point `u₀ ∈ U` is the restriction of the ambient preferred
chart at `u₀` (`TopologicalSpace.Opens.chartAt_eq`), so it evaluates at every point `u : U` as the
ambient chart at `x₀`; and harmonicity of a function on `X` at a point of `U` transports to the
restriction of the function to `U`.  These two facts are the only bookkeeping needed to move the
Green-function data from `Ω` to the space `U`. -/

/-- The chart of the open subspace `U` at `u₀`, evaluated at any point `u : U`, is the ambient
preferred chart at `u₀`, evaluated at `u`. -/
theorem opensChartAt_apply_of_mem (U : TopologicalSpace.Opens X) (u₀ u : U) :
    (chartAt ℂ u₀) u = (chartAt ℂ (u₀ : X)) (u : X) := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := u₀), OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- **Transport of harmonicity to an open subspace.**  A function harmonic on `S ⊆ X` at a point
`z ∈ U` with `(z : X) ∈ S` is harmonic there when read on the open subspace `U`. -/
theorem harmonicOnXAt_restrict {U : TopologicalSpace.Opens X} {u : X → ℝ} {S : Set X}
    (hu : Submission.HarmonicOnX u S) {z : U} (hz : (z : X) ∈ S) :
    Submission.HarmonicOnXAt (fun z : U => u z.1) z := by
  change InnerProductSpace.HarmonicAt
    ((fun z : U => u z.1) ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)
  have hzat : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ (z : X)).symm)
      ((chartAt ℂ (z : X)) (z : X)) := hu (z : X) hz
  have heq : ((fun z : U => u z.1) ∘ (chartAt ℂ z).symm)
      =ᶠ[nhds ((chartAt ℂ (z : X)) (z : X))] (u ∘ (chartAt ℂ (z : X)).symm) := by
    filter_upwards [(chartAt ℂ z).open_target.mem_nhds
      (Work.Modulus.opensChartAt_mem_target U z)] with w hw
    simp only [Function.comp_apply]
    rw [Work.Modulus.opensChartAt_symm_eqOn U z hw]
  rw [Work.Modulus.opensChartAt_apply U z]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hzat

/-- **Transport of holomorphy from an open subspace to the ambient surface.**  If `f` is holomorphic
on all of the open subset `↥U`, then any function on `X` agreeing with `f` on `U` is holomorphic at
every point of `U`. -/
theorem holomorphicOnXAt_of_restrict_eqOn {U : TopologicalSpace.Opens X} {ψ : X → ℂ}
    {f : ↥U → ℂ} (hf : Submission.HolomorphicOnX f Set.univ) {x : X} (hx : x ∈ U)
    (heq : ∀ (y : X) (hy : y ∈ U), ψ y = f ⟨y, hy⟩) : Submission.HolomorphicOnXAt ψ x := by
  rw [Submission.HolomorphicOnXAt]
  set u₀ : ↥U := ⟨x, hx⟩ with hu₀
  have hchart : (chartAt ℂ u₀) u₀ = (chartAt ℂ x) x := Work.Modulus.opensChartAt_apply U u₀
  have hmem : (chartAt ℂ x) x ∈ (chartAt ℂ u₀).target := by
    rw [← hchart]
    exact (chartAt ℂ u₀).map_source (mem_chart_source ℂ u₀)
  have hana : AnalyticAt ℂ (f ∘ (chartAt ℂ u₀).symm) ((chartAt ℂ x) x) := by
    rw [← hchart]
    exact hf u₀ (Set.mem_univ u₀)
  refine hana.congr ?_
  filter_upwards [(chartAt ℂ u₀).open_target.mem_nhds hmem] with z hz
  have hsymm : (((chartAt ℂ u₀).symm z : ↥U) : X) = (chartAt ℂ x).symm z :=
    Work.Modulus.opensChartAt_symm_eqOn U u₀ hz
  show f ((chartAt ℂ u₀).symm z) = ψ ((chartAt ℂ x).symm z)
  rw [heq ((chartAt ℂ x).symm z) (by rw [← hsymm]; exact ((chartAt ℂ u₀).symm z).2)]
  congr 1
  exact Subtype.ext hsymm

/-! ## Local branches of the modulus from the Green-function hypotheses

Since the interface `Submission.HasGreenFunctionE` is unsatisfiable (its superlevel sets `{ε ≤ E}`
cannot be compact near the pole), the local arguments of `Work.Modulus` are restated here with the
hypotheses they actually use: harmonicity off the pole and the bounded logarithmic pole. -/

/-- **The local expansion of a positive harmonic function with a bounded logarithmic pole.**
Hypotheses-only version of `Work.Modulus.localPoleExpansion`: no Green-function data beyond
harmonicity off `z₀` and the two-sided bound of the logarithmic pole on `univ \ {z₀}` is used. -/
theorem localPoleExpansion_of_boundedPole {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ConnectedSpace Y] [SecondCountableTopology Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    {z₀ : Y} {E : Y → ℝ}
    (hharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : ∃ C : ℝ, ∃ V : Set Y, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
      |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ z₀) z₀) ρ) ∧
      (∀ x ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, x ≠ z₀ →
        E x = -Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ + H ((chartAt ℂ z₀) x)) := by
  obtain ⟨C, V, hVnhds, hVbnd⟩ := hpole
  have hsrc : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hsymm₀ : (chartAt ℂ z₀).symm ((chartAt ℂ z₀) z₀) = z₀ :=
    (chartAt ℂ z₀).left_inv hsrc
  have htgt₀ : (chartAt ℂ z₀) z₀ ∈ (chartAt ℂ z₀).target :=
    (chartAt ℂ z₀).map_source hsrc
  have hW : V ∩ (chartAt ℂ z₀).source ∈ 𝓝 z₀ :=
    inter_mem hVnhds ((chartAt ℂ z₀).open_source.mem_nhds hsrc)
  have hpre : (chartAt ℂ z₀).symm ⁻¹' (V ∩ (chartAt ℂ z₀).source) ∈
      𝓝 ((chartAt ℂ z₀) z₀) :=
    ContinuousAt.preimage_mem_nhds
      ((chartAt ℂ z₀).continuousAt_symm htgt₀) (by simpa [hsymm₀] using hW)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ z₀).open_target.mem_nhds htgt₀)
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
      have hEharm : InnerProductSpace.HarmonicAt (E ∘ (chartAt ℂ z₀).symm) z := by
        have h1 : Submission.HarmonicOnXAt E ((chartAt ℂ z₀).symm z) :=
          hharm _ ⟨mem_univ _, hyne⟩
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := E)
          (x := (chartAt ℂ z₀).symm z) (y := z₀) hzpre.2).mp h1
        rwa [hcs] at h2
      have hlogharm : InnerProductSpace.HarmonicAt
          (fun ξ : ℂ => Real.log ‖ξ - (chartAt ℂ z₀) z₀‖) z :=
        AnalyticAt.harmonicAt_log_norm (f := fun ξ : ℂ => ξ - (chartAt ℂ z₀) z₀)
          (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)
      exact hEharm.add hlogharm)
    (fun z hz hzne => by
      have hzR : z ∈ Metric.ball ((chartAt ℂ z₀) z₀) R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hz
      have hzpre : (chartAt ℂ z₀).symm z ∈ V ∩ (chartAt ℂ z₀).source := hRε hzR
      have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm z) = z :=
        (chartAt ℂ z₀).right_inv (hRδ hzR)
      have hyne : (chartAt ℂ z₀).symm z ≠ z₀ := fun hcon => hzne (by rw [← hcs, hcon])
      have h1 := hVbnd ((chartAt ℂ z₀).symm z) hzpre.1 hyne
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

/-- **A branch of the modulus on a chart ball at the pole.** -/
theorem localBranch_at_pole_of_boundedPole {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ConnectedSpace Y] [SecondCountableTopology Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    {z₀ : Y} {E : Y → ℝ}
    (hharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : ∃ C : ℝ, ∃ V : Set Y, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
      |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C) :
    ∃ (ρ : ℝ) (Φ : Y → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch z₀ E (Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  obtain ⟨ρ₀, hρ₀, H, hHharm, hexp⟩ := localPoleExpansion_of_boundedPole hharm hpole
  obtain ⟨F, hFana, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := H) hHharm
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hsrc : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have hatgt : a ∈ c.target := c.map_source hsrc
  have ha_ball : a ∈ Metric.ball a ρ₀ := by simp [Metric.mem_ball, hρ₀]
  set Φ : Y → ℂ := fun y => (c y - a) * Complex.exp (-(F (c y))) with hΦ
  have hev_ball : (Φ ∘ c.symm) =ᶠ[𝓝 a]
      (fun w : ℂ => (w - a) * Complex.exp (-(F w))) := by
    filter_upwards [c.open_target.mem_nhds hatgt, Metric.isOpen_ball.mem_nhds ha_ball]
      with w hwt _
    simp only [Function.comp_apply, hΦ]
    rw [c.right_inv hwt]
  have hmod : ∀ x ∈ Submission.chartBall c a ρ₀, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
    intro x hx hxne
    have hxsrc : x ∈ c.source := hx.1
    have hxball : c x ∈ Metric.ball a ρ₀ := Metric.ball_subset_ball (by linarith) hx.2
    have hcxne : c x ≠ a := fun h => hxne (c.injOn hxsrc hsrc h)
    have hnf : ‖c x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hcxne)
    have hfre : (F (c x)).re = H (c x) := hFre hxball
    have hnorm : ‖Φ x‖ = ‖c x - a‖ * Real.exp (-(H (c x))) := by
      simp only [hΦ, norm_mul, Complex.norm_exp, Complex.neg_re, hfre]
    rw [hnorm, hexp x ⟨hxsrc, hxball⟩ hxne]
    have hlog : Real.exp (Real.log ‖c x - a‖) = ‖c x - a‖ :=
      Real.exp_log (norm_pos_iff.mpr (sub_ne_zero.mpr hcxne))
    have harith : -(-Real.log ‖c x - a‖ + H (c x))
        = Real.log ‖c x - a‖ + (-(H (c x))) := by ring
    rw [harith, Real.exp_add, hlog]
  refine ⟨ρ₀ / 2, Φ, by linarith, ?_, ?_⟩
  · refine ⟨Submission.chartBall_isOpen c a _, ?_, ?_, ?_⟩
    · -- holomorphy
      intro x hx
      have hxsrc : x ∈ c.source := hx.1
      have hxball : c x ∈ Metric.ball a ρ₀ := Metric.ball_subset_ball (by linarith) hx.2
      refine (Submission.HolomorphicOnXAt_iff_chart (f := Φ) (x := x) (y := z₀) hxsrc).mpr ?_
      have hev : (Φ ∘ c.symm) =ᶠ[𝓝 (c x)]
          (fun w : ℂ => (w - a) * Complex.exp (-(F w))) := by
        filter_upwards [c.open_target.mem_nhds (c.map_source hxsrc),
          Metric.isOpen_ball.mem_nhds hxball] with w hwt _
        simp only [Function.comp_apply, hΦ]
        rw [c.right_inv hwt]
      exact ((AnalyticAt.mul (analyticAt_id.sub analyticAt_const)
        (((hFana (c x) hxball).neg).cexp))).congr hev.symm
    · -- non-vanishing off the pole
      intro x hx hxne hzero
      have h := hmod x
        (Work.Modulus.BranchCovering.Aux.chartBall_subset_of_le (by linarith) hx) hxne
      rw [hzero, norm_zero] at h
      exact (Real.exp_ne_zero _) h.symm
    · -- the modulus
      intro x hx hxne
      exact hmod x
        (Work.Modulus.BranchCovering.Aux.chartBall_subset_of_le (by linarith) hx) hxne
  · intro y hy
    by_cases hy0 : y = z₀
    · right
      have hpoleAt : Submission.HasLogPoleAt z₀ Φ :=
        ⟨fun w : ℂ => Complex.exp (-(F w)), ((hFana a ha_ball).neg).cexp,
          Complex.exp_ne_zero _, hev_ball⟩
      have hder : Work.SC.chartDeriv Φ z₀ ≠ 0 :=
        Submission.phi_deriv_ne_zero_of_logPole hpoleAt
      simpa [hy0] using hder
    · left
      intro hzero
      have h := hmod y
        (Work.Modulus.BranchCovering.Aux.chartBall_subset_of_le (by linarith) hy) hy0
      rw [hzero, norm_zero] at h
      exact (Real.exp_ne_zero _) h.symm

/-- **Local branches of the modulus on chart balls, from the hypotheses of a Green function.** -/
theorem exists_localBranch_chartBall_of_boundedPole {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [SecondCountableTopology Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y] {z₀ : Y} {E : Y → ℝ}
    (hharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : ∃ C : ℝ, ∃ V : Set Y, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
      |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C) :
    ∀ x : Y, ∃ (ρ : ℝ) (Φ : Y → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch z₀ E (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  intro x
  rcases eq_or_ne x z₀ with rfl | hxne
  · exact localBranch_at_pole_of_boundedPole hharm hpole
  · have hharmat : Submission.HarmonicOnXAt E x := hharm x ⟨mem_univ x, hxne⟩
    obtain ⟨U₀, Φ, hUo, hxU, hΦhol, hΦne, hΦnorm⟩ :=
      Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt hharmat
    have hbr : Work.SC.IsModulusBranch z₀ E U₀ Φ :=
      ⟨hUo, hΦhol, fun y hy _ => hΦne y hy, fun y hy _ => hΦnorm y hy⟩
    obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ :=
      Work.Modulus.BranchCovering.Aux.exists_chartBall_subset_of_mem_nhds (hUo.mem_nhds hxU)
    refine ⟨ρ₁, Φ, hρ₁, ?_, ?_⟩
    · refine hbr.mono (Submission.chartBall_isOpen _ _ _) hρ₁sub
    · intro y hy
      exact Or.inl (hΦne y (hρ₁sub hy))


/-! ## The modulus of a Green function on a simply connected domain -/

theorem exists_modulusOn {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩs : IsSimplyConnected Ω)
    {x₀ : X} (hx₀ : x₀ ∈ Ω) {E : X → ℝ} (hE : Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E) :
    ∃ Φ : X → ℂ, Work.SimplyConnected.ABS.IsModulusOn Ω x₀ E Φ := by
  classical
  -- the domain `Ω` as an open subspace of `X`
  set U : TopologicalSpace.Opens X := ⟨Ω, hΩo⟩ with hUdef
  have hx₀U : x₀ ∈ U := hx₀
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hΩc
  haveI : SimplyConnectedSpace U := hΩs
  -- the Green-function hypotheses, read on `U`
  have hharmU : Submission.HarmonicOnX (fun z : U => E z.1) (Set.univ \ {⟨x₀, hx₀U⟩}) := by
    intro z hz
    exact harmonicOnXAt_restrict (U := U) hE.2.1
      ⟨z.2, fun h => hz.2 (Subtype.ext h)⟩
  have hpoleU : ∃ C : ℝ, ∃ V : Set U, V ∈ nhds (⟨x₀, hx₀U⟩ : U) ∧
      ∀ u ∈ V, u ≠ (⟨x₀, hx₀U⟩ : U) →
        |E u.1 + Real.log ‖(chartAt ℂ (⟨x₀, hx₀U⟩ : U)) u
          - (chartAt ℂ (⟨x₀, hx₀U⟩ : U)) (⟨x₀, hx₀U⟩ : U)‖| ≤ C := by
    obtain ⟨C, V, hV, hVbnd⟩ := hE.2.2.2
    refine ⟨C, (Subtype.val) ⁻¹' V, ?_, ?_⟩
    · exact (continuous_subtype_val.continuousAt (x := (⟨x₀, hx₀U⟩ : U))).preimage_mem_nhds hV
    · intro u hu hune
      rw [opensChartAt_apply_of_mem U (⟨x₀, hx₀U⟩ : U) u,
        opensChartAt_apply_of_mem U (⟨x₀, hx₀U⟩ : U) (⟨x₀, hx₀U⟩ : U)]
      exact hVbnd u.1 hu u.2 (fun h => hune (Subtype.ext h))
  -- (1) local branches of the modulus on chart balls of `U`
  have hloc : ∀ x : U, ∃ (ρ : ℝ) (Φ : U → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)
        (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) :=
    exists_localBranch_chartBall_of_boundedPole hharmU hpoleU
  -- (2) the branch bundle over the base `U` is a covering space
  have hcov : @IsCoveringMap (Work.SC.ModulusBundle (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)) U
      (Work.SC.modulusBundleTopology (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)) _
      (Work.SC.branchProj (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)) :=
    Work.Modulus.isCoveringMap_branchProj_of_localBranches (z₀ := ⟨x₀, hx₀U⟩)
      (E := fun z : U => E z.1) hloc
  -- (3) the bundle is non-empty: a branch near the pole
  obtain ⟨ρ₀, Φ₀, hρ₀, hbr₀, -⟩ := hloc ⟨x₀, hx₀U⟩
  have hne : (Work.SC.branchSet (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)).Nonempty := by
    refine ⟨(⟨x₀, hx₀U⟩, Φ₀ ⟨x₀, hx₀U⟩, Work.SC.chartDeriv Φ₀ ⟨x₀, hx₀U⟩), ?_⟩
    refine ⟨Submission.chartBall (chartAt ℂ (⟨x₀, hx₀U⟩ : U))
      ((chartAt ℂ (⟨x₀, hx₀U⟩ : U)) (⟨x₀, hx₀U⟩ : U)) ρ₀, Φ₀, hbr₀, ?_⟩
    refine ⟨?_, rfl, rfl⟩
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ (⟨x₀, hx₀U⟩ : U), Metric.mem_ball_self hρ₀⟩
  -- (4) triviality of the monodromy over the simply connected `U`
  obtain ⟨Φ', hΦ'hol, hΦ'ne, hΦ'mod⟩ :=
    Work.SC.exists_holomorphic_modulus_of_isCoveringMap (X := U) (z₀ := ⟨x₀, hx₀U⟩)
      (E := fun z : U => E z.1) hcov hne
  -- (5) extend by `0` outside `Ω` and check the modulus conditions
  set Ψ : X → ℂ := fun x => if hx : x ∈ U then Φ' ⟨x, hx⟩ else 0 with hΨdef
  have hΨeq : ∀ (y : X) (hy : y ∈ U), Ψ y = Φ' ⟨y, hy⟩ := fun y hy => dif_pos hy
  have hholΩ : ∀ x ∈ Ω, Submission.HolomorphicOnXAt Ψ x := fun x hx =>
    holomorphicOnXAt_of_restrict_eqOn hΦ'hol hx hΨeq
  have hmodΩ : ∀ x ∈ Ω, x ≠ x₀ → ‖Ψ x‖ = Real.exp (-(E x)) := by
    intro x hx hxne
    rw [hΨeq x hx]
    exact hΦ'mod ⟨x, hx⟩ (fun h => hxne (congrArg Subtype.val h))
  refine ⟨Ψ, hholΩ, ?_, hmodΩ⟩
  -- (6) the zero at the pole is simple
  exact Work.SimplyConnected.ABS.exists_simpleZero_of_modulus_exp (Ω := Ω) hΩo hx₀ hE.2.2.2
    (hholΩ x₀ hx₀) hmodΩ

end Work.SimplyConnected.ABS
