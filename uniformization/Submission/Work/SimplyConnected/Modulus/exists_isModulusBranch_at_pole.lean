import Mathlib
import Submission.Work.SimplyConnected.ModulusDefs
import Submission.Work.Modulus.localHolomorphicModulus

namespace Work.SimplyConnected.Modulus

open LeanEval.Geometry
open scoped Manifold ContDiff

/-- **A branch of the modulus exists at the pole.**  If `E` is a strong Green function at `z₀`,
then `Work.Modulus.localHolomorphicModulus` produces a holomorphic `Φ` on a chart ball around `z₀`
with a logarithmic pole at `z₀` and modulus `exp (-E)` off the pole.  That chart ball is a
neighbourhood of `z₀` (it is open — `Submission.chartBall_isOpen` — and contains `z₀`, since
`z₀` is in the source of its own chart and `c z₀` is the centre of the ball), and the remaining
condition of `Work.SC.IsModulusBranch`, the non-vanishing of `Φ` off the pole, follows from
`‖Φ x‖ = exp (-(E x)) > 0`. -/
theorem exists_isModulusBranch_at_pole {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E) :
    ∃ (U : Set X) (Φ : X → ℂ), Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ nhds z₀ ∧
      Submission.HasLogPoleAt z₀ Φ := by
  obtain ⟨ρ, Φ, hρ, hhol, hpole, hmod⟩ := Work.Modulus.localHolomorphicModulus hE
  refine ⟨Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, Φ, ?_, ?_, hpole⟩
  · refine ⟨Submission.chartBall_isOpen _ _ _, hhol, ?_, hmod⟩
    intro x hx hxne hzero
    have h := hmod x hx hxne
    rw [hzero, norm_zero] at h
    exact (Real.exp_ne_zero _) h.symm
  · refine (Submission.chartBall_isOpen _ _ _).mem_nhds ?_
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ z₀, Metric.mem_ball_self hρ⟩

end Work.SimplyConnected.Modulus
