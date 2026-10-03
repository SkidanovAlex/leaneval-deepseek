import Mathlib

namespace Work.ORBassSerre.Tree.Geodesic

/-- The vertices of a composite path `u.comp v` are exactly the vertices of `u` together with the vertices of `v`. -/
theorem mem_vertices_comp {V : Type*} [Quiver V] {a b c : V}
    (u : Quiver.Path a b) (v : Quiver.Path b c) (w : V) :
    w ∈ (u.comp v).vertices ↔ w ∈ u.vertices ∨ w ∈ v.vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl (List.mem_of_mem_dropLast h)
    · exact Or.inr h
  · rintro (h | h)
    · by_cases hd : w ∈ u.vertices.dropLast
      · exact Or.inl hd
      · refine Or.inr ?_
        -- `w` lies in `u.vertices` but not in its `dropLast`, hence `w` is the
        -- end vertex `b` of `u`, which is the start vertex of `v`.
        have hmem : w ∈ u.vertices.dropLast ++ [b] := by
          rw [Quiver.Path.dropLast_append_end_eq]; exact h
        rw [List.mem_append, List.mem_singleton] at hmem
        rw [hmem.resolve_left hd]
        exact Quiver.Path.start_mem_vertices v
    · exact Or.inr h

end Work.ORBassSerre.Tree.Geodesic
