import Mathlib
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.Jordan.plane_separation_preconnected_subset
import Submission.Work.Smooth.Jordan.plane_separation_component_U
import Submission.Work.Smooth.Jordan.plane_separation_component_V

/-!
# The two sides of a Jordan curve are determined up to exchange

`PlaneSeparation c` packages the Jordan separation of the trace of a simple closed plane curve `c`
into two open preconnected pieces `U` (unbounded) and `V` (bounded) with `U ∪ V = c.traceᶜ`.

The complement of the trace has exactly two connected components, so a second separation datum `h'`
must have the same two pieces.  Concretely, taking a point `x` of the non-empty set `h.U`, the
connected component of `x` in `c.traceᶜ` is `h.U` (by `plane_separation_component_U`); the same
component computes `h'.U` if `x ∈ h'.U` and `h'.V` if `x ∈ h'.V`.  In the first case `h.U = h'.U`
and in the second `h.U = h'.V`; the companion equality follows because each side is the complement
of the other inside `c.traceᶜ`.
-/

open Set

namespace Work.Smooth.Jordan

theorem plane_separation_eq {c : PlaneCurve} (h h' : PlaneSeparation c) :
    (h.U = h'.U ∧ h.V = h'.V) ∨ (h.U = h'.V ∧ h.V = h'.U) := by
  -- Each side is the complement of the other within `c.traceᶜ`.
  have complV : ∀ hs : PlaneSeparation c, hs.V = c.traceᶜ \ hs.U := by
    intro hs
    ext z
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · rw [← hs.union_eq]; exact Or.inr hz
      · intro hzU; exact Set.disjoint_left.mp hs.disjoint_UV hzU hz
    · rintro ⟨hz, hzU⟩
      have hzu : z ∈ hs.U ∪ hs.V := by rw [hs.union_eq]; exact hz
      rcases hzu with h1 | h1
      · exact absurd h1 hzU
      · exact h1
  have complU : ∀ hs : PlaneSeparation c, hs.U = c.traceᶜ \ hs.V := by
    intro hs
    ext z
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · rw [← hs.union_eq]; exact Or.inl hz
      · intro hzV; exact Set.disjoint_left.mp hs.disjoint_UV hz hzV
    · rintro ⟨hz, hzV⟩
      have hzu : z ∈ hs.U ∪ hs.V := by rw [hs.union_eq]; exact hz
      rcases hzu with h1 | h1
      · exact h1
      · exact absurd h1 hzV
  -- Pick a point of the unbounded side `h.U`.
  obtain ⟨x, hx⟩ := h.nonempty_U
  have hx_trace : x ∉ c.trace := by
    have hsub : h.U ⊆ c.traceᶜ := by rw [← h.union_eq]; exact Set.subset_union_left
    exact hsub hx
  have hx' : x ∈ h'.U ∨ x ∈ h'.V := by
    have : x ∈ h'.U ∪ h'.V := by rw [h'.union_eq]; exact hx_trace
    exact this
  -- The connected component of `x` computes `h.U`.
  have hcomp : connectedComponentIn c.traceᶜ x = h.U := plane_separation_component_U h hx
  rcases hx' with hxU | hxV
  · left
    have hcomp' : connectedComponentIn c.traceᶜ x = h'.U := plane_separation_component_U h' hxU
    have hUeq : h.U = h'.U := by rw [← hcomp, hcomp']
    exact ⟨hUeq, by rw [complV h, complV h', hUeq]⟩
  · right
    have hcomp' : connectedComponentIn c.traceᶜ x = h'.V := plane_separation_component_V h' hxV
    have hUeq : h.U = h'.V := by rw [← hcomp, hcomp']
    exact ⟨hUeq, by rw [complV h, complU h', hUeq]⟩

end Work.Smooth.Jordan
