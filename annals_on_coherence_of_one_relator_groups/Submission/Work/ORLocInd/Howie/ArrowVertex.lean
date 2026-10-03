/-
# The arrows of a path and its vertex list

For a path `p : Quiver.Path a b`, the `k`-th arrow of `p.arrowList` has source the `k`-th vertex of
`p.vertices.dropLast` and target the `k`-th vertex of `p.vertices.tail`.  Concretely,

* `arrowList_map_left  : p.arrowList.map Quiver.Total.left  = p.vertices.dropLast`;
* `arrowList_map_right : p.arrowList.map Quiver.Total.right = p.vertices.tail`.

These two list identities are the bridge between the two descriptions of a path (as a list of
arrows and as a list of vertices) used by the combinatorial arguments about labellings.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Mathlib.Combinatorics.Quiver.Path.Vertices

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V]

/-- The sources of the arrows of a path are the vertices of the path without its last vertex. -/
theorem arrowList_map_left {a b : V} (p : Quiver.Path a b) :
    p.arrowList.map Quiver.Total.left = p.vertices.dropLast := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Quiver.Path.arrowList_cons, List.map_append, ih, Quiver.Path.vertices_cons,
      List.concat_eq_append]
    simp only [List.map_cons, List.map_nil]
    rw [List.dropLast_concat]
    exact Quiver.Path.dropLast_append_end_eq p

/-- The targets of the arrows of a path are the vertices of the path without its first vertex. -/
theorem arrowList_map_right {a b : V} (p : Quiver.Path a b) :
    p.arrowList.map Quiver.Total.right = p.vertices.tail := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Quiver.Path.arrowList_cons, List.map_append, ih, Quiver.Path.vertices_cons,
      List.concat_eq_append]
    simp only [List.map_cons, List.map_nil]
    exact (List.tail_append_singleton_of_ne_nil (Quiver.Path.vertices_ne_nil p)).symm

end Work.ORLocInd.Howie
