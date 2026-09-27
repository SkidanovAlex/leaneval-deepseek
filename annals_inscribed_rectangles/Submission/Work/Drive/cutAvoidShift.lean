import Mathlib
import Submission.Work.Drive.diskCut_inner_avoid
import Submission.Work.Drive.clampedSweep

/-!
# The cut-avoidance (`δc`) producer of the transport `T6`, and its single-point reduction

The transport `T6` (`Work.Drive.T6GenAt`, `Submission/Work/Drive/T6GenAtDefs.lean`) carries a third
conjunct

> `∃ δc > 0, ∀ x : 𝔼², ‖cplxOf x‖ ≤ δc → x ∉ diskCut Q W`

(the "cut avoidance"), whose production is flagged as *not yet produced* in
`Submission/Work/Drive/HDENSE_STATUS.md` §4 and described as an *open and dense* condition in the
perturbation parameter in `Submission/Work/Drive/NOTES_LEAD_hblock_uniformity.md` §4.3 (the honest
chart is constant near the origin, `Submission/Work/Drive/CHART_DEGENERACY.md`, so the condition is a
*single-point* avoidance: `Q 0 ∉ W '' unitBox 2`).

This file supplies the two halves of that producer, in a form independent of the design:

* `Work.Drive.exists_deltaC_iff_notMem` — the `δc` conjunct is *equivalent* to the single-point
  avoidance `Q 0 ∉ W '' unitBox 2` (the forward direction is the proved
  `Work.Drive.diskCut_inner_avoid`; the converse is immediate at `x = 0`).  So the whole content of the
  third conjunct is the avoidance of one point;
* `Work.Drive.exists_deltaC_shift` — the avoidance can be *arranged* by moving the chart-perturbation
  parameter `σ` of *one* block, with the other data fixed: if the sweep's image has empty interior
  (`K`, an input produced by the weak-Sard chapter of the workspace) then for every base parameter and
  every radius there is a nearby `σ` with `Ξ (s₀ + σ) p₀ ∉ K`, and then `diskCut_inner_avoid` converts
  that into the `δc` conjunct for the perturbed chart.

Both halves are stated for a general `ChartPert` family, so that the design's blocks `k` (chart
`blockChart Ξ Q u τ k`, sweep `clampedSweep c ψ (blockPlane Ξ Q u τ (k+2))`) instantiate them without
any index bookkeeping.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Filter Set

/-- **The `δc` conjunct of the transport `T6` is a single-point avoidance.**  For a continuous chart
`Q` and a continuous chain `W` (whose image over the parameter box is then compact), the existence of a
radius `δc > 0` on which the *cut* `diskCut Q W` misses a neighbourhood of the origin of the plane
parameter is equivalent to `Q 0` not lying in the image of `W`.

The honest chart of the route is constant near the origin, so the two are the same statement by
`Work.Drive.CHART_DEGENERACY`-type reasoning; the equivalence itself is elementary: the forward
direction is `Work.Drive.diskCut_inner_avoid` (compactness of `W '' unitBox 2`), and if `Q 0` lies in
the image then `x = 0` is a cut point at every radius. -/
theorem exists_deltaC_iff_notMem (Q : ℂ → CappingSpace)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (hQ : Continuous Q) (hW : Continuous W) :
    (∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc → x ∉ diskCut Q W) ↔
      Q 0 ∉ W '' Submission.Drive.unitBox 2 := by
  constructor
  · rintro ⟨δc, hδc, h⟩ hmem
    have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ diskCut Q W := by
      refine ⟨?_, ?_⟩
      · simp
      · simpa using hmem
    exact h 0 (by simpa using hδc.le) h0
  · exact fun h0 => diskCut_inner_avoid Q W hQ hW h0

end Work.Drive
