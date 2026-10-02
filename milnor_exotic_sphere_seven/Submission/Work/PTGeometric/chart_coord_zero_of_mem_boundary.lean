import Mathlib
import Submission.Work.PTGeometric.halfBallPiece_coord_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `0`-th chart coordinate vanishes at a boundary point

Let `W` be a `T²` space charted in the half-space model `EuclideanHalfSpace (n + 1)` and carrying a
`C¹` manifold-with-boundary structure.  This file proves

* `Work.PTGeometric.isInteriorPoint_iff_coord_pos` — **the chart criterion for the interior**:
  a point `x` in the source of a chart `e` of the atlas is an interior point of `W` if and only if
  the `0`-th coordinate of `e x` is positive;
* `Work.PTGeometric.chart_coord_zero_of_mem_boundary` — **the target**: a boundary point `z` of `W`
  lying in the source of the chart at `y` has vanishing `0`-th coordinate in that chart, i.e.
  `((chartAt _ y) z).1 0 = 0`.

Together with the already proved `Work.PTGeometric.coord_pos_of_mem_chart_source` (the direct
implication "interior ⟹ positive coordinate") this pins down the boundary of `W` inside any chart of
the atlas as the hyperplane `{v | v 0 = 0}` — the chart-independence of the boundary of a manifold
with boundary.

## Proof outline

* `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas` reduces the (chart-free) notion of interior
  point to membership of the extended chart image in the interior of the extended chart target;
* `OpenPartialHomeomorph.interior_extend_target_subset_interior_range` and
  `interior_range_modelWithCornersEuclideanHalfSpace` identify the *forward* direction with
  `0 < (e x) 0`, while `OpenPartialHomeomorph.mem_interior_extend_target` gives the converse;
* the target follows since the two notions "interior point" and "boundary point" are complementary
  (`ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint`) and the `0`-th coordinate of a point
  of the half space is always nonnegative (it is the subtype condition defining
  `EuclideanHalfSpace`).
-/

open scoped Manifold

namespace Work.PTGeometric

/-- **The chart criterion for interior points.**  For a `C¹` manifold with boundary `W` modelled on
the half-space `EuclideanHalfSpace (n + 1)`, a point `x` of the source of a chart `e` of the atlas
is an interior point if and only if the `0`-th coordinate of its chart image `e x` is positive. -/
theorem isInteriorPoint_iff_coord_pos {n : ℕ} (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {e : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) W) {x : W} (hx : x ∈ e.source) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint x ↔ 0 < (e x).1 0 := by
  -- A `C¹` manifold: the chart at `x` detects interior points.
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas
    (I := modelWithCornersEuclideanHalfSpace (n + 1)) hn he hx]
  constructor
  · -- The extended chart target is contained in the model space, whose interior is `{v | 0 < v 0}`.
    intro h
    have h' := OpenPartialHomeomorph.interior_extend_target_subset_interior_range
      (I := modelWithCornersEuclideanHalfSpace (n + 1)) e h
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h'
    simpa [OpenPartialHomeomorph.extend_coe, modelWithCornersEuclideanHalfSpace_toFun] using h'
  · -- Conversely, a positive `0`-th coordinate lands in the interior of the model space.
    intro h
    refine OpenPartialHomeomorph.mem_interior_extend_target e (e.map_source hx) ?_
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa [modelWithCornersEuclideanHalfSpace_toFun] using h

/-- **In a chart of the atlas, the `0`-th coordinate of a boundary point vanishes.**  If `z` is a
boundary point of `W` lying in the source of the chart at `y`, then the `0`-th coordinate of the
chart image of `z` is `0`. -/
theorem chart_coord_zero_of_mem_boundary (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y z : W} (hzsrc : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source)
    (hzb : z ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 0 = 0 := by
  -- The boundary point `z` is not an interior point.
  have hb : (modelWithCornersEuclideanHalfSpace (n + 1)).IsBoundaryPoint z := hzb
  have hnot : ¬ (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint z :=
    fun h => ((ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint
      (I := modelWithCornersEuclideanHalfSpace (n + 1)) z).1 h) hb
  -- Hence its chart coordinate is not positive …
  have hle : ¬ 0 < ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 0 := fun h =>
    hnot ((isInteriorPoint_iff_coord_pos W (chart_mem_atlas (EuclideanHalfSpace (n + 1)) y)
      hzsrc).2 h)
  -- … and the half-space condition makes it nonnegative.
  exact le_antisymm (not_lt.mp hle)
    ((chartAt (EuclideanHalfSpace (n + 1)) y) z).2

end Work.PTGeometric
