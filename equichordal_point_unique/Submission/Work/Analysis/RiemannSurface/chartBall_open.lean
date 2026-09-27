import Mathlib
import Submission.RiemannSurface

/-!
# The chart ball is open (first brick of the shell cover, `NOTES_…` §39.7)

`Submission.chartBall c a ρ = c.source ∩ c ⁻¹' Metric.ball a ρ` is open in `X`: on the (open) source
of the chart `c` it is the preimage of the open ball, and the junk values of `c` outside the source are
removed by the intersection.  The clean proof is the identity with the *image* form,

  `chartBall c a ρ = c.symm '' (Metric.ball a ρ ∩ c.target)`,

which holds by `map_source`/`left_inv` in one direction and `map_target`/`right_inv` in the other;
openness then follows from `OpenPartialHomeomorph.isOpen_image_of_subset_source` applied to the open
ball intersected with the (open) target (the pattern used in the workspace, e.g.
`Submission/Work/SimplyConnected/ABS/developing_map_exists.lean`).

A finite cover of a compact set by open chart balls needs exactly `IsOpen (chartBall …)` for
`IsCompact.elim_finite_subcover`; this is the first ingredient of the shell cover of
`Analysis/RiemannSurface/exists_dbar_weight`.
-/

open scoped Topology Manifold

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem chartBall_eq_image (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    Submission.chartBall c a ρ = c.symm '' (Metric.ball a ρ ∩ c.target) := by
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    exact ⟨c x, ⟨hxb, c.map_source hx⟩, c.left_inv hx⟩
  · rintro ⟨w, ⟨hw, hwt⟩, rfl⟩
    refine ⟨c.map_target hwt, ?_⟩
    show c (c.symm w) ∈ Metric.ball a ρ
    rw [c.right_inv hwt]
    exact hw

theorem isOpen_chartBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    IsOpen (Submission.chartBall c a ρ) := by
  rw [chartBall_eq_image]
  exact (c.symm).isOpen_image_of_subset_source (Metric.isOpen_ball.inter c.open_target)
    fun y hy => hy.2

end Work.Analysis.RiemannSurface
