import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Geodesic

/-- Every vertex of `u` is a vertex of `u.comp v` (the composite path lists the vertices of `u`,
then those of `v` after the common end vertex). -/
theorem mem_vertices_comp_left {V : Type*} [Quiver V] {a b c : V} (u : Quiver.Path a b)
    (v : Quiver.Path b c) {w : V} (hw : w ∈ u.vertices) : w ∈ (u.comp v).vertices := by
  rw [Quiver.Path.vertices_comp]
  have hw' : w ∈ u.vertices.dropLast ++ [b] := by
    rw [Quiver.Path.dropLast_append_end_eq]
    exact hw
  rcases List.mem_append.mp hw' with h | h
  · exact List.mem_append_left _ h
  · rw [List.mem_singleton] at h
    rw [h]
    exact List.mem_append_right _ (Quiver.Path.start_mem_vertices v)

/-- A subpath of a reduced path is reduced: if `u.comp v` is reduced, then so is `v`.
(A backtrack in `v` would already be a backtrack in `u.comp v`.) -/
theorem isReduced_of_comp_right' {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    {u : Quiver.Path a b} {v : Quiver.Path b c} (h : (u.comp v).IsReduced) : v.IsReduced :=
  fun q hq => h (u.comp q) (hq.comp_left u)

/-- A reduced path through a vertex `m` splits at `m` into two reduced subpaths whose vertices are vertices of the whole path. -/
theorem exists_decomp_of_mem_vertices {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    {p : Quiver.Path a b} (hp : p.IsReduced) {m : V} (hm : m ∈ p.vertices) :
    ∃ (u : Quiver.Path a m) (v : Quiver.Path m b), u.IsReduced ∧ v.IsReduced ∧
      u.comp v = p ∧ (∀ w, w ∈ u.vertices → w ∈ p.vertices) ∧
      (∀ w, w ∈ v.vertices → w ∈ p.vertices) := by
  obtain ⟨u, v, huv⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hm
  refine ⟨u, v, ?_, ?_, huv.symm, ?_, ?_⟩
  · rw [huv] at hp; exact hp.of_comp
  · rw [huv] at hp; exact isReduced_of_comp_right' hp
  · intro w hw; rw [huv]; exact mem_vertices_comp_left u v hw
  · intro w hw; rw [huv, Quiver.Path.vertices_comp]; exact List.mem_append_right _ hw

end Work.ORBassSerre.Tree.Geodesic
