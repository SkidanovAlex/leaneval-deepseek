import Mathlib
import Submission.Work.Smooth.Jordan.Separation

/-!
# The bounded side of a Jordan curve is a connected component of the complement

`PlaneSeparation c` packages the Jordan separation theorem for a simple closed plane curve `c`:
the complement of the trace of `c` is the disjoint union of two non-empty preconnected open sets,
the *outside* `U` and the *inside* `V`, the latter being bounded.

The complement of the trace is *not* connected — `V` is bounded while the complement is not — so
the connected components of `c.traceᶜ` are exactly the two pieces `U` and `V`.  Here we prove the
statement for the bounded piece: for `x ∈ V`, the connected component of `x` in the subspace
`c.traceᶜ` is all of `V`.

The argument is a direct application of `IsPreconnected.subset_or_subset`: any preconnected subset
of `c.traceᶜ` must lie inside one of the two disjoint open pieces `U`, `V`, because those two
pieces are open, disjoint and cover `c.traceᶜ`.  Applying this to the connected component of `x`
and using `x ∈ V` rules out the `U` alternative, while `V` is itself preconnected and contains
`x`, giving the reverse inclusion through `IsPreconnected.subset_connectedComponentIn`.
-/

open Set

namespace Work.Smooth.Jordan

theorem plane_separation_component_V {c : PlaneCurve} (h : PlaneSeparation c) {x : ℂ}
    (hx : x ∈ h.V) : connectedComponentIn c.traceᶜ x = h.V := by
  -- The bounded piece is contained in the complement of the trace.
  have hVsub : h.V ⊆ c.traceᶜ := by
    rw [← h.union_eq]; exact Set.subset_union_right
  have hx' : x ∈ c.traceᶜ := hVsub hx
  -- `x` lies in its own connected component inside `c.traceᶜ`.
  have hxcomp : x ∈ connectedComponentIn c.traceᶜ x := by
    rw [connectedComponentIn_eq_image hx']
    exact ⟨⟨x, hx'⟩, mem_connectedComponent, rfl⟩
  -- `V` is preconnected and contains `x`, so it sits inside the component.
  refine Set.Subset.antisymm ?_ (h.preconn_V.subset_connectedComponentIn hx hVsub)
  -- The component lies in `U` or in `V`, since `U`, `V` are disjoint open sets covering the
  -- complement of the trace.
  rcases (isPreconnected_connectedComponentIn (F := c.traceᶜ) (x := x)).subset_or_subset
      h.isOpen_U h.isOpen_V h.disjoint_UV
      (by rw [h.union_eq]; exact connectedComponentIn_subset _ _) with hU | hV
  · -- It cannot lie in `U`: it contains `x ∈ V`, and `U`, `V` are disjoint.
    exact absurd (Set.disjoint_left.mp h.disjoint_UV (hU hxcomp) hx) (by simp)
  · exact hV

end Work.Smooth.Jordan
