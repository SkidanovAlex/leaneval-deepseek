import Mathlib
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Convex.reducedSpan_subset_of_mem

namespace Work.ORBassSerre.Tree.Convex

open Quiver

/-! ## Auxiliary path lemmas

Small general facts about vertex lists of concatenated paths, used in the proof of the
three-point property of reduced spans below.  These are kept private to this file. -/

/-- The right factor of a reduced concatenation of paths is reduced. -/
private theorem qpath_isReduced_of_comp_right {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b c : V} {p : Quiver.Path a b} {q : Quiver.Path b c} (h : (p.comp q).IsReduced) :
    q.IsReduced :=
  fun r hr => h (p.comp r) (hr.comp_left p)

/-- Every vertex of a path is a vertex of any extension of that path. -/
private theorem qpath_vertices_subset_comp_right {V : Type*} [Quiver V] {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) : q.vertices ⊆ (p.comp q).vertices := by
  rw [Quiver.Path.vertices_comp]
  exact List.Sublist.subset (List.sublist_append_right _ _)

/-- **Three point property of a tree.**  A vertex lying on the reduced span from `u` to `w` lies
on the reduced span from `u` to `z` or on the reduced span from `w` to `z`. -/
private theorem qpath_reducedSpan_or {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (h : Work.ORBassSerre.IsTree V) (u w z : V) {v : V}
    (hv : v ∈ Work.ORBassSerre.reducedSpan u w) :
    v ∈ Work.ORBassSerre.reducedSpan u z ∨ v ∈ Work.ORBassSerre.reducedSpan w z := by
  classical
  -- split the given reduced path from `u` to `w` through `v`
  obtain ⟨p, hp, hvp⟩ := hv
  obtain ⟨A, B, hAB⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hvp
  have hp' : (A.comp B).IsReduced := hAB ▸ hp
  have hA : A.IsReduced := Quiver.Path.IsReduced.of_comp hp'
  have hB : B.IsReduced := qpath_isReduced_of_comp_right hp'
  -- a reduced path from `v` to `z`
  set q := h.geodesic v z with hq_def
  have hq : q.IsReduced := h.geodesic_isReduced v z
  by_cases hred : (A.comp q).IsReduced
  · -- `A` followed by `q` is already reduced: it is a reduced path from `u` to `z` through `v`
    exact Or.inl ⟨A.comp q, hred, qpath_vertices_subset_comp_right A q (Quiver.Path.start_mem_vertices q)⟩
  · -- otherwise the backtrack sits at the junction, and the first arrow of `q` points back along `A`
    obtain ⟨w', hw'⟩ : ∃ w', Quiver.Path.DeleteBacktrack (A.comp q) w' := by
      simpa only [Quiver.Path.IsReduced, not_forall, not_not] using hred
    obtain ⟨x, f, A', q', hAeq, hqeq, -⟩ :=
      Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_comp_junction hA hq hw'
    -- so `w ↝ z` through `v` is reduced
    have hBcomm : (B.reverse.comp q).IsReduced := by
      by_contra hnot
      obtain ⟨R, hR⟩ : ∃ R, Quiver.Path.DeleteBacktrack (B.reverse.comp q) R := by
        simpa only [Quiver.Path.IsReduced, not_forall, not_not] using hnot
      obtain ⟨y, g, B'', q'', hBeq, hqeq2, -⟩ :=
        Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_comp_junction
          (Quiver.Path.IsReduced.reverse hB) hq hR
      -- both decompositions exhibit the first arrow of `q`, so `f = g`
      have hqrev_f : q.reverse = (q'.reverse).cons f := by
        rw [hqeq, Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath, Quiver.reverse_reverse,
          Quiver.Path.comp_toPath_eq_cons]
      have hqrev_g : q.reverse = (q''.reverse).cons g := by
        rw [hqeq2, Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath, Quiver.reverse_reverse,
          Quiver.Path.comp_toPath_eq_cons]
      have h1 : (q'.reverse).cons f = (q''.reverse).cons g := hqrev_f.symm.trans hqrev_g
      have hob := Quiver.Path.obj_eq_of_cons_eq_cons h1
      have hheq : HEq f g := Quiver.Path.hom_heq_of_cons_eq_cons h1
      subst hob
      have hfg : f = g := eq_of_heq hheq
      -- hence `B` starts with the reverse of `f`, and `A · B` has a backtrack at the junction
      have hBrev : B = (Quiver.reverse f).toPath.comp B''.reverse := by
        have h2 : B.reverse = B''.cons f := by rw [hBeq, ← hfg]
        have h3 : B = (B''.cons f).reverse := by rw [← h2, Quiver.Path.reverse_reverse]
        rw [h3]
        rfl
      have h1' : A.comp B
          = (A'.comp f.toPath).comp ((Quiver.reverse f).toPath.comp B''.reverse) := by
        rw [hAeq, hBrev, Quiver.Path.comp_toPath_eq_cons]
      have h2' : (A'.comp f.toPath).comp ((Quiver.reverse f).toPath.comp B''.reverse)
          = A'.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp B''.reverse)) :=
        Quiver.Path.comp_assoc A' f.toPath _
      have hABeq : A.comp B
          = A'.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp B''.reverse)) :=
        h1'.trans h2'
      have hdb : Quiver.Path.DeleteBacktrack (A.comp B) (A'.comp B''.reverse) := by
        rw [hABeq]
        exact Quiver.Path.DeleteBacktrack.intro A' f B''.reverse
      exact hp' _ hdb
    exact Or.inr
      ⟨B.reverse.comp q, hBcomm, qpath_vertices_subset_comp_right B.reverse q (Quiver.Path.start_mem_vertices q)⟩

/-- The convex hull of any set of vertices of a tree is convex. -/
theorem isConvexSet_hull {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (h : Work.ORBassSerre.IsTree V) (X : Set V) :
    Work.ORBassSerre.IsConvexSet (Work.ORBassSerre.hull X) := by
  rintro a ⟨x₁, hx₁, y₁, hy₁, ha⟩ b ⟨x₂, hx₂, y₂, hy₂, hb⟩ p hp v hv
  -- `v` lies on the span from `a` to `b`; locate it on the three spans through `x₁`, `x₂`
  have hvab : v ∈ Work.ORBassSerre.reducedSpan a b := ⟨p, hp, hv⟩
  rcases qpath_reducedSpan_or h a b x₂ hvab with h1 | h1
  · -- `v ∈ [a,x₂]`
    rcases qpath_reducedSpan_or h a x₂ x₁ h1 with h2 | h2
    · -- `v ∈ [a,x₁]`
      rcases qpath_reducedSpan_or h a x₁ y₁ h2 with h3 | h3
      · exact ⟨x₁, hx₁, y₁, hy₁, (reducedSpan_subset_of_mem h ha).1 h3⟩
      · exact ⟨x₁, hx₁, y₁, hy₁, h3⟩
    · exact ⟨x₂, hx₂, x₁, hx₁, h2⟩
  · -- `v ∈ [b,x₂]`
    rcases qpath_reducedSpan_or h b x₂ y₂ h1 with h2 | h2
    · exact ⟨x₂, hx₂, y₂, hy₂, (reducedSpan_subset_of_mem h hb).1 h2⟩
    · exact ⟨x₂, hx₂, y₂, hy₂, h2⟩

end Work.ORBassSerre.Tree.Convex
