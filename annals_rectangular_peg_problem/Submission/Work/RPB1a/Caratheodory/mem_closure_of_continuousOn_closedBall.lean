import Mathlib

namespace Work.RPB1a.Caratheodory

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- A continuous map on the closed unit disc whose values on the open disc lie in `D` takes its
values at every point of the unit circle in the closure of `D`. -/
theorem mem_closure_of_continuousOn_closedBall {D : Set ℂ} {Ψ : ℂ → ℂ}
    (hΨc : ContinuousOn Ψ (closedBall 0 1)) (hΨs : Ψ '' ball 0 1 = D) {ζ : ℂ}
    (hζ : ζ ∈ sphere 0 1) : Ψ ζ ∈ closure D := by
  -- The circle point lies in the closure of the open disc, hence in the closed disc.
  have hζcB : ζ ∈ closedBall 0 1 := sphere_subset_closedBall hζ
  have hζcl : ζ ∈ closure (ball 0 1) := by
    rw [closure_ball 0 one_ne_zero]
    exact hζcB
  -- Restrict continuity to the open disc and push the accumulation point through `Ψ`.
  have hcont : ContinuousWithinAt Ψ (ball 0 1) ζ :=
    (hΨc ζ hζcB).mono ball_subset_closedBall
  have h := hcont.mem_closure_image hζcl
  rwa [hΨs] at h

end Work.RPB1a.Caratheodory
