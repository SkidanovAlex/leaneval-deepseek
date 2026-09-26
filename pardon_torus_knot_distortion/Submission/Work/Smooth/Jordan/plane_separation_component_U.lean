import Mathlib
import Submission.Work.Smooth.Jordan.Separation

namespace Work.Smooth.Jordan

/-- The connected component of a point of the unbounded side `h.U` of a Jordan separation is
`h.U` itself: `h.U` is preconnected and meets no other side, and conversely any preconnected
subset of the complement of the trace containing `x` cannot cross from `h.U` to `h.V` because
those two are disjoint non-empty open sets covering `c.traceᶜ`. -/
theorem plane_separation_component_U {c : PlaneCurve} (h : PlaneSeparation c) {x : ℂ} (hx : x ∈ h.U) : connectedComponentIn c.traceᶜ x = h.U := by
  have hUsub : h.U ⊆ c.traceᶜ := by
    rw [← h.union_eq]; exact Set.subset_union_left
  have hx' : x ∈ c.traceᶜ := hUsub hx
  refine le_antisymm ?_ ?_
  · -- the component is a preconnected subset of `U ∪ V`, and it meets `U`, so it lies in `U`
    have hsub : connectedComponentIn c.traceᶜ x ⊆ h.U ∪ h.V := by
      rw [h.union_eq]; exact connectedComponentIn_subset _ _
    have hne : (connectedComponentIn c.traceᶜ x ∩ h.U).Nonempty :=
      ⟨x, mem_connectedComponentIn hx', hx⟩
    exact IsPreconnected.subset_left_of_subset_union h.isOpen_U h.isOpen_V h.disjoint_UV hsub hne
      isPreconnected_connectedComponentIn
  · -- `U` is preconnected and contains `x`, so it lies in the component
    exact h.preconn_U.subset_connectedComponentIn hx hUsub

end Work.Smooth.Jordan
