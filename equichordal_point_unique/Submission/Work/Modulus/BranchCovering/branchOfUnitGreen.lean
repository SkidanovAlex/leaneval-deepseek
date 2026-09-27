import Mathlib
import Submission.Work.Modulus.Defs
import Submission.Work.Modulus.localHolomorphicModulus
import Submission.Work.SimplyConnected.ModulusDefs
import Submission.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne

/-!
# Branches of the modulus from unit-pole Green data

The local-branch statements of the modulus bundle `Work.SC.branchProj z₀ E` that the chapter needs
exist in the parallel development `Work.SimplyConnected.Modulus` for the *unsatisfiable* predicate
`Work.UnitGreen.IsUnitGreenFunctionAt`.  The two used here are restated for the satisfiable
`Work.UnitGreen.IsUnitGreenFunctionAt`:

* off the pole, only harmonicity of `E` at the point is needed
  (`Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt`, which has no
  Green-function hypothesis at all);
* at the pole, the local model branch comes from `Work.Modulus.localHolomorphicModulus` (the local
  pole expansion of the Green function), which is stated for the unit-pole predicate.

Both statements are non-vacuous: the hypothesis is satisfied by the Green function of the upper
half plane.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Modulus.BranchCovering

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

namespace Aux

/-- **A local branch of the modulus at a point different from the pole** (unit-pole Green data). -/
theorem exists_isModulusBranch_of_ne_of_unitGreen {z₀ x : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) (hx : x ≠ z₀) :
    ∃ (U : Set X) (Φ : X → ℂ), Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ nhds x ∧ Φ x ≠ 0 := by
  have hharm : Submission.HarmonicOnXAt E x := hE.1.2.1 x ⟨mem_univ x, hx⟩
  obtain ⟨U, Φ, hUopen, hxU, hΦhol, hΦne, hΦnorm⟩ :=
    Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt (X := X) hharm
  exact ⟨U, Φ, ⟨hUopen, hΦhol, fun y hy _ => hΦne y hy, fun y hy _ => hΦnorm y hy⟩,
    hUopen.mem_nhds hxU, hΦne x hxU⟩

/-- **A model branch of the modulus at the pole** (unit-pole Green data): a holomorphic `Φ` on a
chart ball around `z₀` with a logarithmic pole there and modulus `exp (-E)` off the pole. -/
theorem exists_isModulusBranch_at_pole_of_unitGreen {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ∃ (U : Set X) (Φ : X → ℂ), Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ nhds z₀ ∧
      Submission.HasLogPoleAt z₀ Φ := by
  obtain ⟨ρ, Φ, hρ, hhol, hpole, hmod⟩ :=
    Work.Modulus.localHolomorphicModulus_of_unitGreen (z₀ := z₀) (E := E) hE
  refine ⟨Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, Φ, ?_, ?_, hpole⟩
  · refine ⟨Submission.chartBall_isOpen _ _ _, hhol, ?_, hmod⟩
    intro x hx hxne hzero
    have h := hmod x hx hxne
    rw [hzero, norm_zero] at h
    exact (Real.exp_ne_zero _) h.symm
  · refine (Submission.chartBall_isOpen _ _ _).mem_nhds ?_
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ z₀, Metric.mem_ball_self hρ⟩

end Aux

end Work.Modulus.BranchCovering
