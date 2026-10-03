import Mathlib
import Submission.Work.ORBassSerre.Tree.Convex

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-- Reversing a path reverses its list of vertices. -/
theorem vertices_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) : p.reverse.vertices = p.vertices.reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((Quiver.reverse e).toPath.comp p.reverse).vertices = (p.cons e).vertices.reverse
    rw [Path.vertices_comp, Path.vertices_toPath, ih, Path.vertices_cons]
    simp

/-- A vertex lies on a path iff it lies on the reversed path. -/
theorem mem_vertices_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) (v : V) : v ∈ p.reverse.vertices ↔ v ∈ p.vertices := by
  rw [vertices_reverse]
  exact List.mem_reverse

/-- The set of vertices lying on a reduced path from `a` to `b` is contained in the one from
`b` to `a`: reverse the path. -/
theorem reducedSpan_subset_reverse {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (a b : V) : Work.ORBassSerre.reducedSpan a b ⊆ Work.ORBassSerre.reducedSpan b a :=
  fun _ ⟨p, hp, hv⟩ => ⟨p.reverse, hp.reverse, (mem_vertices_reverse p _).mpr hv⟩

/-- The set of vertices lying on a reduced path from `a` to `b` depends only on the unordered
pair `{a, b}`: `reducedSpan` is symmetric. -/
theorem reducedSpan_comm {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] (a b : V) :
    Work.ORBassSerre.reducedSpan a b = Work.ORBassSerre.reducedSpan b a :=
  Set.Subset.antisymm (reducedSpan_subset_reverse a b) (reducedSpan_subset_reverse b a)

end Work.ORBassSerre.Tree.Seg
