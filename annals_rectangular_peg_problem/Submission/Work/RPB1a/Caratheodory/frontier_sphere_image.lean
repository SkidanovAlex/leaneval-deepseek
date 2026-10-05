import Mathlib

namespace Work.RPB1a.Caratheodory

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- A continuous map on the closed unit disc whose image on the open disc is `D` and which maps the
unit sphere into `frontier D` maps the unit sphere *onto* `frontier D`: the frontier is contained
in the image of the closed disc, which is the image of the open disc together with the image of the
sphere. -/
theorem image_sphere_eq_frontier {D : Set ℂ} (hDo : IsOpen D) {Ψ : ℂ → ℂ}
    (hΨc : ContinuousOn Ψ (closedBall 0 1)) (hΨs : Ψ '' ball 0 1 = D)
    (hmt : MapsTo Ψ (sphere 0 1) (frontier D)) :
    Ψ '' sphere 0 1 = frontier D := by
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨z, hz, rfl⟩
    exact hmt hz
  intro y hy
  rw [IsOpen.frontier_eq hDo] at hy
  obtain ⟨hycl, hyD⟩ := hy
  -- the closed image of the disc is closed and contains the image of the open disc
  have hclosed : IsClosed (Ψ '' closedBall 0 1) :=
    (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hΨc |>.isClosed
  have hcl : closure D ⊆ Ψ '' closedBall 0 1 := by
    rw [← hΨs]
    exact closure_minimal (image_mono ball_subset_closedBall) hclosed
  have hymem : y ∈ Ψ '' closedBall 0 1 := hcl hycl
  rw [← Metric.ball_union_sphere, image_union] at hymem
  rcases hymem with h | h
  · rw [hΨs] at h
    exact absurd h hyD
  · exact h

end Work.RPB1a.Caratheodory
