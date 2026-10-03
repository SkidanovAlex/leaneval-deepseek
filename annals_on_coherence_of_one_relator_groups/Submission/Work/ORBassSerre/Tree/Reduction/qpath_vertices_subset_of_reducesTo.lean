import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Quiver

namespace Path

variable {V : Type*} [Quiver V] [Quiver.HasReverse V]
variable {a b c : V}

/-- Deleting one backtrack can only remove vertices from a path: the vertex list of the
result is a sublist of the vertex list of the original path. -/
theorem DeleteBacktrack.vertices_sublist {p q : Path a b} (h : DeleteBacktrack p q) :
    q.vertices.Sublist p.vertices := by
  cases h with
  | intro p₁ e p₂ =>
    show (p₁.comp p₂).vertices.Sublist
      (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))).vertices
    simp only [Path.vertices_comp]
    rw [← List.append_assoc (e.toPath.vertices.dropLast)]
    exact (List.Sublist.refl _).append (List.sublist_append_right _ _)

end Path

end Quiver

namespace Work.ORBassSerre.Tree.Reduction

open Quiver

/-- Deleting backtracks only removes vertices from a path. -/
theorem qpath_vertices_subset_of_reducesTo {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b : V} {p q : Quiver.Path a b} (h : p.ReducesTo q) :
    ∀ v ∈ q.vertices, v ∈ p.vertices := by
  induction h with
  | refl => exact fun _ hv => hv
  | tail _ hstep ih => exact fun v hv => ih v (hstep.vertices_sublist.subset hv)

end Work.ORBassSerre.Tree.Reduction
