import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.coveringAux
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_at_pole
import Submission.Lib.Unif2.Work.Modulus.localPoleExpansion
import Submission.Lib.Unif2.Work.Modulus.localHolomorphicModulus
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_injective_holomorphicOn_of_isSimplyConnected_open
import Submission.Lib.Unif2.Work.Potential.removable_singularity_bounded_harmonic
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_branch_chartBall_off_pole

namespace Work.SimplyConnected.ABS

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set Classical

/-! ## Chart bookkeeping for an open subspace

The chart of an open subset `U ⊆ X` at a point `x` is the restriction of the ambient chart at `x`
(`TopologicalSpace.Opens.chartAt_eq`).  The two lemmas below spell out the two consequences used
throughout: chart balls of the subspace are the preimages of chart balls of the ambient surface, and
the chart derivative of a function pulled back from the ambient surface is the ambient chart
derivative. -/

section Transport

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The chart ball of an open subspace is the preimage of the ambient chart ball.** -/
theorem subtype_val_preimage_chartBall (U : TopologicalSpace.Opens X) (x : U) (ρ : ℝ) :
    Subtype.val ⁻¹' (Submission.chartBall (chartAt ℂ (x : X)) ((chartAt ℂ (x : X)) (x : X)) ρ)
      = Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ := by
  have h1 : (chartAt ℂ x).source = Subtype.val ⁻¹' (chartAt ℂ (x : X)).source := by
    rw [TopologicalSpace.Opens.chartAt_eq]
    exact OpenPartialHomeomorph.subtypeRestr_source (chartAt ℂ (x : X)) ⟨x⟩
  have h2 : ∀ y : U, (chartAt ℂ x) y = (chartAt ℂ (x : X)) y.1 := by
    intro y
    rw [TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_coe (chartAt ℂ (x : X)) ⟨x⟩, Set.domRestrict_apply]
  have h3 : (chartAt ℂ x) x = (chartAt ℂ (x : X)) (x : X) :=
    Work.Modulus.opensChartAt_apply U x
  ext y
  rw [Set.mem_preimage, Submission.mem_chartBall, Submission.mem_chartBall, h1, h2 y, h3]
  simp only [Set.mem_preimage]

/-- Membership in a chart ball of an open subspace, in ambient terms. -/
theorem mem_chartBall_subtype (U : TopologicalSpace.Opens X) (x : U) (ρ : ℝ) (y : U) :
    y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ ↔
      (y : X) ∈ Submission.chartBall (chartAt ℂ (x : X)) ((chartAt ℂ (x : X)) (x : X)) ρ := by
  have h := subtype_val_preimage_chartBall U x ρ
  constructor
  · intro hy
    rw [← h] at hy
    simpa using hy
  · intro hy
    rw [← h]
    simpa using hy

end Transport

section SubtypeTransport

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Holomorphy is insensitive to passing to an open subspace.** -/
theorem holomorphicOnXAt_subtype_val {U : TopologicalSpace.Opens X} {Ψ : X → ℂ} (x : U)
    (h : Submission.HolomorphicOnXAt Ψ (x : X)) :
    Submission.HolomorphicOnXAt (X := U) (fun z : U => Ψ z.1) x := by
  rw [Submission.HolomorphicOnXAt] at h ⊢
  rw [Work.Modulus.opensChartAt_apply U x]
  have hev : (fun z : U => Ψ z.1) ∘ (chartAt ℂ x).symm
      =ᶠ[𝓝 ((chartAt ℂ (x : X)) (x : X))] Ψ ∘ (chartAt ℂ (x : X)).symm := by
    have h' : (chartAt ℂ (x : X)).symm
        =ᶠ[𝓝 ((chartAt ℂ (x : X)) (x : X))] Subtype.val ∘ (chartAt ℂ x).symm :=
      TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq U
    filter_upwards [h'] with w hw
    simp only [Function.comp_apply] at hw ⊢
    rw [← hw]
  exact h.congr hev.symm

/-- **The chart derivative is insensitive to passing to an open subspace.** -/
theorem chartDeriv_subtype_val {U : TopologicalSpace.Opens X} {Ψ : X → ℂ} (x : U) :
    Work.SC.chartDeriv (X := U) (fun z : U => Ψ z.1) x = Work.SC.chartDeriv Ψ (x : X) := by
  rw [Work.SC.chartDeriv, Work.SC.chartDeriv, Work.Modulus.opensChartAt_apply U x]
  have hev : (fun z : U => Ψ z.1) ∘ (chartAt ℂ x).symm
      =ᶠ[𝓝 ((chartAt ℂ (x : X)) (x : X))] Ψ ∘ (chartAt ℂ (x : X)).symm := by
    have h' : (chartAt ℂ (x : X)).symm
        =ᶠ[𝓝 ((chartAt ℂ (x : X)) (x : X))] Subtype.val ∘ (chartAt ℂ x).symm :=
      TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq U
    filter_upwards [h'] with w hw
    simp only [Function.comp_apply] at hw ⊢
    rw [← hw]
  exact hev.deriv_eq

end SubtypeTransport

/-! ## The pole case

At the pole `x₀` the modulus has a simple zero, and the branch is
`Φ y = ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀) · exp (-(F ((chartAt ℂ x₀) y)))`, where `F` is a local
analytic function whose real part is the harmonic remainder `H` of the local expansion
`E = -log ‖(chartAt ℂ x₀) · - (chartAt ℂ x₀) x₀‖ + H` of `E` at its logarithmic pole. -/

section Pole

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The local branch of the modulus at the pole, from the local expansion of `E`.**

`hexp` is the conclusion of `Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn`: in the
preferred chart `c = chartAt ℂ x₀`, `E` has the form `E x = -log ‖c x - c x₀‖ + H (c x)` with `H`
harmonic on the disc of radius `ρ` around `c x₀` and `E > 0`-free on `U`.  Writing `H = Re F` for
`F` analytic on that disc, the function `Φ y = (c y - c x₀) · exp (-(F (c y)))` is a holomorphic
branch of `exp (-E)` on the chart ball of radius `ρ/2` around the pole of the open subspace `U`: the
prefactor supplies the zero at `x₀` and
`‖Φ y‖ = ‖c y - c x₀‖ · exp (-H (c y)) = exp (-(-log ‖c y - c x₀‖ + H (c y))) = exp (-(E y))`
off the pole.  The pair `(Φ, chartDeriv Φ)` is non-degenerate on that ball: `Φ` does not vanish off
the pole, and at the pole `chartDeriv Φ x₀ = exp (-(F (c x₀))) ≠ 0`. -/
theorem exists_branch_chartBall_at_pole_of_expansion {U : TopologicalSpace.Opens X} {x₀ : X}
    (hx₀ : x₀ ∈ U) {E : X → ℝ}
    (hexp : ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ x₀) x₀) ρ) ∧
      (∀ x : X, x ∈ (U : Set X) →
        x ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ → x ≠ x₀ →
        E x = -Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ + H ((chartAt ℂ x₀) x))) :
    ∃ (ρ : ℝ) (Φ : U → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch (⟨x₀, hx₀⟩ : U) (fun z : U => E z.1)
        (Submission.chartBall (chartAt ℂ (⟨x₀, hx₀⟩ : U))
          ((chartAt ℂ (⟨x₀, hx₀⟩ : U)) (⟨x₀, hx₀⟩ : U)) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ (⟨x₀, hx₀⟩ : U))
          ((chartAt ℂ (⟨x₀, hx₀⟩ : U)) (⟨x₀, hx₀⟩ : U)) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  obtain ⟨ρ₀, hρ₀, H, hHharm, hexp'⟩ := hexp
  obtain ⟨F, hFana, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hHharm
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have ha_ball : (chartAt ℂ x₀) x₀ ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ₀ :=
    Metric.mem_ball_self hρ₀
  set Ψ : X → ℂ :=
    fun y => ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀) *
      Complex.exp (-(F ((chartAt ℂ x₀) y))) with hΨ
  -- membership of the points of the chart ball of the subspace in the ambient chart balls
  have hmemHalf : ∀ y : U, y ∈ Submission.chartBall (chartAt ℂ (⟨x₀, hx₀⟩ : U))
        ((chartAt ℂ (⟨x₀, hx₀⟩ : U)) (⟨x₀, hx₀⟩ : U)) (ρ₀ / 2) →
      (y : X) ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) (ρ₀ / 2) := by
    intro y hy
    have h := (mem_chartBall_subtype U (⟨x₀, hx₀⟩ : U) (ρ₀ / 2) y).mp hy
    simpa using h
  have hmemFull : ∀ y : U, y ∈ Submission.chartBall (chartAt ℂ (⟨x₀, hx₀⟩ : U))
        ((chartAt ℂ (⟨x₀, hx₀⟩ : U)) (⟨x₀, hx₀⟩ : U)) (ρ₀ / 2) →
      (y : X) ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ₀ := by
    intro y hy
    have h := hmemHalf y hy
    rw [Submission.mem_chartBall] at h ⊢
    exact ⟨h.1, Metric.ball_subset_ball (by linarith) h.2⟩
  -- the ambient holomorphy of `Ψ` on the chart ball of radius `ρ₀ / 2`
  have hhol : ∀ y : X, y ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) (ρ₀ / 2) →
      Submission.HolomorphicOnXAt Ψ y := by
    intro y hy
    rw [Submission.mem_chartBall] at hy
    obtain ⟨hysrc, hyball⟩ := hy
    have hyball' : (chartAt ℂ x₀) y ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ₀ :=
      Metric.ball_subset_ball (by linarith) hyball
    refine (Submission.HolomorphicOnXAt_iff_chart (f := Ψ) (x := y) (y := x₀) hysrc).mpr ?_
    have hev : (Ψ ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) y)]
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * Complex.exp (-(F w))) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hysrc), Metric.isOpen_ball.mem_nhds hyball'] with w hwt _hw
      simp only [Function.comp_apply, hΨ]
      rw [(chartAt ℂ x₀).right_inv hwt]
    exact ((AnalyticAt.mul (analyticAt_id.sub analyticAt_const)
      (((hFana ((chartAt ℂ x₀) y) hyball').neg).cexp)).congr hev.symm)
  -- a point of the chart ball which is not the pole has chart value different from the centre
  have hne_centre : ∀ y : U, (y : X) ∈ Submission.chartBall (chartAt ℂ x₀)
        ((chartAt ℂ x₀) x₀) ρ₀ → y ≠ (⟨x₀, hx₀⟩ : U) →
      (chartAt ℂ x₀) y ≠ (chartAt ℂ x₀) x₀ := by
    intro y hy hyne hcon
    have hyne' : (y : X) ≠ x₀ := fun h => hyne (Subtype.ext h)
    exact hyne' ((chartAt ℂ x₀).injOn hy.1 hsrc hcon)
  refine ⟨ρ₀ / 2, fun y : U => Ψ y.1, by linarith, ?_, ?_⟩
  · refine ⟨Submission.chartBall_isOpen _ _ _, ?_, ?_, ?_⟩
    · -- holomorphy on the chart ball of the subspace
      intro y hy
      exact holomorphicOnXAt_subtype_val y (hhol y.1 (hmemHalf y hy))
    · -- non-vanishing off the pole
      intro y hy hyne
      have hfull := hmemFull y hy
      have hcne := hne_centre y hfull hyne
      show Ψ (y : X) ≠ 0
      rw [hΨ]
      exact mul_ne_zero (sub_ne_zero.mpr hcne) (Complex.exp_ne_zero _)
    · -- the modulus
      intro y hy hyne
      have hhalf := hmemHalf y hy
      have hfull := hmemFull y hy
      have hcne := hne_centre y hfull hyne
      have hyne' : (y : X) ≠ x₀ := fun h => hyne (Subtype.ext h)
      have hHval : (F ((chartAt ℂ x₀) y)).re = H ((chartAt ℂ x₀) y) := hFre hfull.2
      have hE := hexp' (y : X) y.2 hfull hyne'
      have hnorm : ‖Ψ (y : X)‖ =
          ‖(chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀‖ * Real.exp (-(H ((chartAt ℂ x₀) y))) := by
        rw [hΨ]
        simp only [norm_mul, Complex.norm_exp, Complex.neg_re, hHval]
      show ‖Ψ (y : X)‖ = Real.exp (-(E (y : X)))
      rw [hnorm, hE]
      have hlog : Real.exp (Real.log ‖(chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀‖)
          = ‖(chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀‖ :=
        Real.exp_log (norm_pos_iff.mpr (sub_ne_zero.mpr hcne))
      have harith : -( -Real.log ‖(chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀‖ + H ((chartAt ℂ x₀) y))
          = Real.log ‖(chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀‖ + (-(H ((chartAt ℂ x₀) y))) := by
        ring
      rw [harith, Real.exp_add, hlog]
  · -- the pair `(Φ, chartDeriv Φ)` is non-degenerate on the chart ball
    intro y hy
    by_cases hyne : y = (⟨x₀, hx₀⟩ : U)
    · right
      subst hyne
      rw [chartDeriv_subtype_val (U := U) (Ψ := Ψ) (x := (⟨x₀, hx₀⟩ : U))]
      rw [Work.SC.chartDeriv]
      change deriv (Ψ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0
      have hev : (Ψ ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
          (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * Complex.exp (-(F w))) := by
        filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
          ((chartAt ℂ x₀).map_source hsrc), Metric.isOpen_ball.mem_nhds ha_ball] with w hwt _hw
        simp only [Function.comp_apply, hΨ]
        rw [(chartAt ℂ x₀).right_inv hwt]
      rw [hev.deriv_eq]
      have hder : deriv (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * Complex.exp (-(F w)))
          ((chartAt ℂ x₀) x₀) = Complex.exp (-(F ((chartAt ℂ x₀) x₀))) := by
        have h1 : HasDerivAt (fun w : ℂ => w - (chartAt ℂ x₀) x₀) 1 ((chartAt ℂ x₀) x₀) :=
          (hasDerivAt_id ((chartAt ℂ x₀) x₀)).sub_const ((chartAt ℂ x₀) x₀)
        have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-(F w)))
            (deriv (fun w : ℂ => Complex.exp (-(F w))) ((chartAt ℂ x₀) x₀))
            ((chartAt ℂ x₀) x₀) :=
          ((hFana ((chartAt ℂ x₀) x₀) ha_ball).neg.cexp).differentiableAt.hasDerivAt
        have hmul : HasDerivAt (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * Complex.exp (-(F w)))
            (1 * Complex.exp (-(F ((chartAt ℂ x₀) x₀))) +
              ((chartAt ℂ x₀) x₀ - (chartAt ℂ x₀) x₀) *
                deriv (fun w : ℂ => Complex.exp (-(F w))) ((chartAt ℂ x₀) x₀))
            ((chartAt ℂ x₀) x₀) := h1.mul h2
        rw [hmul.deriv]
        simp
      rw [hder]
      exact Complex.exp_ne_zero _
    · left
      have hfull := hmemFull y hy
      have hcne := hne_centre y hfull hyne
      show Ψ (y : X) ≠ 0
      rw [hΨ]
      exact mul_ne_zero (sub_ne_zero.mpr hcne) (Complex.exp_ne_zero _)

end Pole

/-- **Local branches of the holomorphic modulus `exp (-E)` on chart balls of an open subspace.**

`U` is an open subset of a Riemann surface `X`, and `E : X → ℝ` satisfies the *satisfiable* hypotheses of
Anghel--Bruin--Stan's disc result (item 10 of arXiv:2008.12189) as formalised in
`Work.SimplyConnected.ABS.IsGreenOn (U : Set X) x₀ E`: `E > 0` on `U ∖ {x₀}`, `E` harmonic on
`U ∖ {x₀}`, and a bounded logarithmic pole at `x₀` in the preferred chart (`HasLogPoleOn`).  (This is
deliberately *not* `Submission.HasGreenFunctionE`, whose superlevel hypothesis -- `{ε ≤ E}` compact for
every `ε > 0` -- is unsatisfiable, since it fails in every punctured neighbourhood of the pole.)

Reading `E` on the open subspace `U ⊆ X` as `fun z : U => E z.1`, the claim is that every point `x : U`
has a chart ball carrying a *branch* of the modulus: a holomorphic `Φ : U → ℂ` which does not vanish off
the pole and has `‖Φ y‖ = exp (-(E y))` there, and whose pair (value, chart derivative,
`Work.SC.chartDeriv`) never vanishes on that ball.

Recipes.  Write `z₀ := (⟨x₀, hx₀⟩ : U)`.

* At the pole `x = z₀`: the pole bound says that in the preferred chart `c = chartAt ℂ z₀` the function
`w ↦ E (c.symm w) + log ‖w - c z₀‖` is bounded on a punctured disc; a bounded harmonic function on a
punctured disc extends across the puncture (`Work.Potential.removable_singularity_bounded_harmonic`), so
`E (c.symm w) = -log ‖w - c z₀‖ + H w` for `H` harmonic on a ball.  Writing `H = Re F` with `F` analytic
on that ball (`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), the function
`Φ x := (c x - c z₀) * Complex.exp (-(F (c x)))` is such a branch; the pair is non-degenerate because
`Φ` is nonzero off the pole and `chartDeriv Φ z₀ = Complex.exp (-(F (c z₀))) ≠ 0`.  This is
`Work.Modulus.localPoleExpansion` `+` `Work.Modulus.localHolomorphicModulus` with `HasGreenFunctionE`
replaced by the hypotheses above.

* Off the pole `x ≠ z₀`: `E` is harmonic at `x`, so `Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt`
(available, no Green-function hypotheses) gives a branch on a neighbourhood of `x`; shrink it to a chart
ball with `Work.Modulus.BranchCovering.Aux.exists_chartBall_subset_of_mem_nhds`, and make the ball avoid
the pole with `Work.Modulus.BranchCovering.Aux.exists_chartBall_avoiding` (this is the argument of
`Work.Modulus.BranchCovering.Aux.exists_isModulusBranch_chartBall_off_pole`).

The statement is the exact `hloc` input consumed by the covering statement for the branch bundle. -/
theorem exists_localBranch_chartBall_of_isGreenOn {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : TopologicalSpace.Opens X} {x₀ : X} (hx₀ : x₀ ∈ U) {E : X → ℝ}
    (hE : Work.SimplyConnected.ABS.IsGreenOn (U : Set X) x₀ E) :
    ∀ x : U, ∃ (ρ : ℝ) (Φ : U → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch (⟨x₀, hx₀⟩ : U) (fun z : U => E z.1)
        (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  intro x
  rcases eq_or_ne x (⟨x₀, hx₀⟩ : U) with hx | hx
  · subst hx
    exact exists_branch_chartBall_at_pole_of_expansion hx₀
      (Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn
        ((U.2).mem_nhds hx₀) hE.2.1 hE.2.2.2)
  · exact exists_branch_chartBall_off_pole hx₀ hE hx

end

end Work.SimplyConnected.ABS
