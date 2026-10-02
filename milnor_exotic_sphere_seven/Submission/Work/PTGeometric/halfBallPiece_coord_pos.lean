import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfRestrictIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `0`-th chart coordinate is positive at an interior point of a half-ball piece

Let `W` be a `T²` space charted in the half-space model `𝓡∂ (n+1)` and carrying a `C¹`
manifold-with-boundary structure.  For a coordinate half-ball piece
`K = Work.Orient.halfBallPiece (n + 1) W z r` (the chart-`z` preimage of a small ambient ball), a
point `x ∈ K` which is **not** a boundary point of `W` has strictly positive `0`-th coordinate in
the chart at `z`.

The half-ball piece enters only through `x ∈ (chartAt _ z).source`; the actual content is the
chart-independence of the interior:
* an interior point of `W` is a point whose image in *any* chart lies in the interior of (the
  extended target of) that chart (`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`);
* the extended target of a chart is contained in `range 𝓡∂ (n+1)`, whose interior is
  `{y | 0 < y 0}` (`interior_range_modelWithCornersEuclideanHalfSpace`).

## Main lemmas

* `Work.PTGeometric.coord_pos_of_mem_chart_source` — the general statement for an interior point in
  the source of a chart;
* `Work.PTGeometric.halfBallPiece_coord_pos` — the stated form, for a point of a half-ball piece.
-/

set_option linter.unusedVariables false

open scoped Manifold
open Set

namespace Work.PTGeometric

/-- **The `0`-th coordinate of a chart is positive at an interior point.**  If `x` is an interior
point of `W` lying in the source of the chart at `z`, then the extended chart at `z` maps `x` to a
point with strictly positive `0`-th coordinate. -/
theorem coord_pos_of_mem_chart_source (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {z x : W} (hxsrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source)
    (hint : (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint x) :
    0 < (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z x) 0 := by
  -- The chart at `z` detects interior points (`C¹` manifold): `x` maps into the interior of the
  -- extended target of the chart.
  have hmem : ((chartAt (EuclideanHalfSpace (n + 1)) z).extend
        (modelWithCornersEuclideanHalfSpace (n + 1))) x ∈
      interior ((chartAt (EuclideanHalfSpace (n + 1)) z).extend
        (modelWithCornersEuclideanHalfSpace (n + 1))).target :=
    (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas
      (I := modelWithCornersEuclideanHalfSpace (n + 1)) (M := W) (n := (1 : WithTop ℕ∞))
      (by norm_num) (chart_mem_atlas _ z) hxsrc).1 hint
  -- The extended target is contained in the model space, whose interior is `{y | 0 < y 0}`.
  have hrange : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z x) ∈
      interior (range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
    have := interior_mono
      (extChartAt_target_subset_range (I := modelWithCornersEuclideanHalfSpace (n + 1)) z) hmem
    simpa using this
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at hrange
  exact hrange

/-- **The `0`-th coordinate of the chart at `z` is positive on the interior part of a coordinate
half-ball piece.** -/
theorem halfBallPiece_coord_pos (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (z : W) (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W z r) :
    ∀ x ∈ Work.Orient.halfBallPiece (n + 1) W z r,
        x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        0 < (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z x) 0 := by
  intro x hx hxb
  -- A point of the piece lies in the source of the chart at `z` …
  have hxsrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source := hx.2
  -- … and not being a boundary point means it is an interior point.
  have hint : (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint x :=
    (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint
      (I := modelWithCornersEuclideanHalfSpace (n + 1)) x).2 hxb
  exact coord_pos_of_mem_chart_source n W hxsrc hint

end Work.PTGeometric
