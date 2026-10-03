import Mathlib

namespace Work.ORBassSerre.Tree.Geodesic

/-- Reversing a path does not change its set of vertices. -/
theorem mem_vertices_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) (w : V) : w ∈ p.reverse.vertices ↔ w ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Quiver.Path.reverse, Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath,
      Quiver.Path.vertices_cons, List.concat_eq_append] at *
    simp_all
    tauto

end Work.ORBassSerre.Tree.Geodesic
