import Mathlib

/-!
# Components of a finite union of equal closed balls are at positive distance

A point outside a connected component of a finite union of closed balls is at positive distance from
that component: the union is closed (so the component is closed, being the image of a connected
component of the subtype), and a closed nonempty set keeps its outside points at positive
`Metric.infDist`.  This is the bookkeeping that lets a loop in the frontier of the component of `0`
be seen as a loop in the frontier of the whole union: the other components sit at positive distance.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **A finite union of equal closed balls is closed.** -/
theorem isClosed_biUnion_closedBall {P : Finset ℂ} {r : ℝ} :
    IsClosed (⋃ w ∈ P, Metric.closedBall w r) :=
  isClosed_biUnion_finset fun _ _ => Metric.isClosed_closedBall

/-- **A component of a finite union of closed balls is closed.** -/
theorem isClosed_connectedComponentIn_union {P : Finset ℂ} {r : ℝ} {y : ℂ}
    (hy : y ∈ ⋃ w ∈ P, Metric.closedBall w r) :
    IsClosed (connectedComponentIn (⋃ w ∈ P, Metric.closedBall w r) y) := by
  rw [connectedComponentIn_eq_image hy]
  exact (isClosed_biUnion_closedBall (P := P) (r := r)).isClosedEmbedding_subtypeVal.isClosedMap _
    isClosed_connectedComponent

/-- **Positive distance from a component.** -/
theorem pos_infDist_componentIn {P : Finset ℂ} {r : ℝ} {x y : ℂ}
    (hy : y ∈ ⋃ w ∈ P, Metric.closedBall w r)
    (h : x ∉ connectedComponentIn (⋃ w ∈ P, Metric.closedBall w r) y) :
    0 < Metric.infDist x (connectedComponentIn (⋃ w ∈ P, Metric.closedBall w r) y) :=
  (isClosed_connectedComponentIn_union hy).notMem_iff_infDist_pos
    ⟨y, mem_connectedComponentIn hy⟩ |>.mp h

end

end Work.Smooth.SphereJordan
