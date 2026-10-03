import Mathlib
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Convex

open Quiver

section PathHelpers

variable {V : Type*} [Quiver V] {a b c : V}

/-- If a concatenation of paths is reduced, then so is its right factor. -/
private theorem IsReduced.of_comp_right [Quiver.HasReverse V]
    {p : Quiver.Path a b} {q : Quiver.Path b c} (h : (p.comp q).IsReduced) : q.IsReduced :=
  fun r hr => h (p.comp r) (hr.comp_left p)

/-- The vertex list of a path `p` is `p.vertices.dropLast` followed by the endpoint of `p`. -/
private theorem vertices_eq_dropLast_append_end (p : Quiver.Path a b) :
    p.vertices = p.vertices.dropLast ++ [b] := by
  have h := Quiver.Path.vertices_comp (a := a) p (Quiver.Path.nil : Quiver.Path b b)
  rw [Quiver.Path.comp_nil, Quiver.Path.vertices_nil] at h
  exact h

/-- Every vertex of a path is a vertex of any extension of that path. -/
private theorem vertices_subset_comp_left (p : Quiver.Path a b) (q : Quiver.Path b c) :
    p.vertices ⊆ (p.comp q).vertices := by
  intro v hv
  rw [vertices_eq_dropLast_append_end p] at hv
  rcases List.mem_append.mp hv with h | h
  · rw [Quiver.Path.vertices_comp]
    exact List.mem_append.mpr (Or.inl h)
  · rw [Quiver.Path.vertices_comp]
    have hvb : v = b := by simpa using h
    rw [hvb]
    exact List.mem_append.mpr (Or.inr (Quiver.Path.start_mem_vertices q))

/-- Every vertex of a path is a vertex of any extension of that path. -/
private theorem vertices_subset_comp_right (p : Quiver.Path a b) (q : Quiver.Path b c) :
    q.vertices ⊆ (p.comp q).vertices := by
  intro v hv
  rw [Quiver.Path.vertices_comp]
  exact List.mem_append.mpr (Or.inr hv)

end PathHelpers

/-- In a tree, if `c` lies on the reduced span from `a` to `b`, then the segments from `c` to `b`
and from `a` to `c` are contained in the span from `a` to `b`. -/
theorem reducedSpan_subset_of_mem {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (h : Work.ORBassSerre.IsTree V) {a b c : V}
    (hc : c ∈ Work.ORBassSerre.reducedSpan a b) :
    Work.ORBassSerre.reducedSpan c b ⊆ Work.ORBassSerre.reducedSpan a b ∧
      Work.ORBassSerre.reducedSpan a c ⊆ Work.ORBassSerre.reducedSpan a b := by
  obtain ⟨p, hp, hcp⟩ := hc
  -- split a reduced path from `a` to `b` through `c` at the vertex `c`
  obtain ⟨p₁, p₂, hp_eq⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hcp
  have hp_comp : (p₁.comp p₂).IsReduced := hp_eq ▸ hp
  have hp₁ : p₁.IsReduced := Quiver.Path.IsReduced.of_comp hp_comp
  have hp₂ : p₂.IsReduced := IsReduced.of_comp_right hp_comp
  constructor
  · -- the segment from `c` to `b`: its reduced paths are the suffix `p₂`
    rintro v ⟨r, hr, hrv⟩
    have hr' : r = p₂ := Tree.Geodesic.qpath_eq_of_isTree h hr hp₂
    refine ⟨p, hp, ?_⟩
    rw [hp_eq]
    exact vertices_subset_comp_right p₁ p₂ (hr' ▸ hrv)
  · -- the segment from `a` to `c`: its reduced paths are the prefix `p₁`
    rintro v ⟨r, hr, hrv⟩
    have hr' : r = p₁ := Tree.Geodesic.qpath_eq_of_isTree h hr hp₁
    refine ⟨p, hp, ?_⟩
    rw [hp_eq]
    exact vertices_subset_comp_left p₁ p₂ (hr' ▸ hrv)

end Work.ORBassSerre.Tree.Convex
