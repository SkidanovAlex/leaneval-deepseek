import Mathlib
import Submission.RiemannSurface
import Submission.Holomorphic
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Commons.Geometry.Manifold.harmonicAt_pullback_iff_chart
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd

/-!
# A harmonic function on a chart ball is the real part of a holomorphic function

This module proves the **local** statement

> if `u` is harmonic on the chart ball `chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ` (whose
> closed version sits inside the chart's target), then there is `F : X → ℂ`, holomorphic on that
> ball, with `(F y).re = u y` for every `y` in it,

i.e. `Work.SimplyConnected.ABS.exists_holomorphicOnX_re_of_harmonicOn_chartBall`.

This is the brick that the closed superlevel form of the ABS filling step needs (see
`NOTES_region_with_sector_boundary_STATUS.md` §W–§X): every landed conjugate construction in the
workspace (`Submission/Conjugate.lean`: `exists_conjData`, `isCoveringMap_fst_conjTopology`,
`exists_holomorphicOnX_re_of_harmonic`) assumes `HarmonicOnX u Set.univ`, i.e. *global*
harmonicity, so none of them reaches a harmonic function defined only on a region such as
`Ω \ {x₀}`.  The proof here transports the statement to the chart coordinates, where it is the
Mathlib theorem `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`
(`Mathlib/Analysis/Complex/Harmonic/Analytic.lean`), and transports the resulting analytic function
back along the chart.  The two transports use the landed chart-independence lemmas
`Commons.Geometry.Manifold.harmonicAt_pullback_iff_chart` and
`Commons.Geometry.Manifold.chart_transition_analyticOnNhd`.

Downstream (delegated separately): on a chart ball, `u ≡ c` near one point implies `u ≡ c` on the
whole ball, by the landed holomorphic identity theorem
`Work.SimplyConnected.Modulus.eqOn_chartBall_of_eventuallyEq`; and the resulting clopen argument on
the preconnected `Ω \ {x₀}` gives the identity theorem for harmonic functions, hence the closed
superlevel connectedness.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A harmonic function on a chart ball is the real part of a holomorphic function.** -/
theorem exists_holomorphicOnX_re_of_harmonicOn_chartBall {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target) {u : X → ℝ}
    (hu : Submission.HarmonicOnX u (Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ)) :
    ∃ F : X → ℂ,
      Submission.HolomorphicOnX F (Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ) ∧
      ∀ y ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ, (F y).re = u y := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  -- the coordinate expression of `u` is harmonic on the Euclidean ball
  have hharm : InnerProductSpace.HarmonicOnNhd (fun w : ℂ => u (c.symm w))
      (Metric.ball (c x₀) ρ) := by
    intro w hw
    have hwt : w ∈ c.target := hsub (Metric.ball_subset_closedBall hw)
    have hxs : c.symm w ∈ c.source := c.map_target hwt
    have hmem : c.symm w ∈ Submission.chartBall c (c x₀) ρ :=
      ⟨hxs, by rw [Set.mem_preimage, c.right_inv hwt]; exact hw⟩
    have h1 : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ (c.symm w)).symm)
        ((chartAt ℂ (c.symm w)) (c.symm w)) := hu _ hmem
    have h3 := (Commons.Geometry.Manifold.harmonicAt_pullback_iff_chart (u := u)
      (x := c.symm w) (y := x₀) hxs).mp h1
    rw [c.right_inv hwt] at h3
    exact h3
  obtain ⟨F, hFana, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm
  refine ⟨fun y => F (c y), ?_, ?_⟩
  · intro y hy
    obtain ⟨hys, hyb⟩ := Submission.mem_chartBall.mp hy
    -- the transition from the preferred chart at `y` to the preferred chart at `x₀` is analytic
    have htr : AnalyticAt ℂ ((chartAt ℂ y).symm.trans c) ((chartAt ℂ y) y) := by
      have hmem : (chartAt ℂ y) y ∈ ((chartAt ℂ y).symm.trans c).source := by
        rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
        refine ⟨(chartAt ℂ y).map_source (mem_chart_source ℂ y), ?_⟩
        rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
        exact hys
      exact Commons.Geometry.Manifold.chart_transition_analyticOnNhd y x₀ _ hmem
    have h1 : AnalyticAt ℂ F (c y) := hFana (c y) hyb
    have h2 : AnalyticAt ℂ (fun z : ℂ => F (c ((chartAt ℂ y).symm z)))
        ((chartAt ℂ y) y) := by
      refine h1.comp_of_eq ?_ ?_
      · exact htr
      · rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    show AnalyticAt ℂ (fun z : ℂ => F (c ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y)
    exact h2
  · intro y hy
    obtain ⟨hys, hyb⟩ := Submission.mem_chartBall.mp hy
    have h1 : (F (c y)).re = u (c.symm (c y)) := hFre hyb
    rw [c.left_inv hys] at h1
    exact h1

end Work.SimplyConnected.ABS
