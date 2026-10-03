import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-! ## Path bookkeeping (private copies, so that this file is self-contained)

A few elementary facts about the list of vertices of a `Quiver.Path` that the argument needs.
They are kept `private` so that they cannot collide with the (identical) public lemmas that
other files of the development provide. -/

private theorem vertices_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) : p.reverse.vertices = p.vertices.reverse := by
  induction p with
  | nil => rfl
  | cons p' e ih =>
    have hr : (p'.cons e).reverse = (Quiver.reverse e).toPath.comp p'.reverse := rfl
    rw [hr, Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath, ih, Quiver.Path.vertices_cons,
      List.concat_eq_append, List.reverse_concat]
    rfl

private theorem mem_vertices_reverse_iff {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) {v : V} : v ∈ p.reverse.vertices ↔ v ∈ p.vertices := by
  rw [vertices_reverse, List.mem_reverse]

private theorem isReduced_of_comp_right {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    {p : Quiver.Path a b} {q : Quiver.Path b c} (h : (p.comp q).IsReduced) : q.IsReduced :=
  fun r hr => h (p.comp r) (hr.comp_left p)

private theorem mem_vertices_comp_left {V : Type*} [Quiver V] {a b c : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} {v : V} (hv : v ∈ p.vertices) : v ∈ (p.comp q).vertices := by
  induction q with
  | nil => exact hv
  | cons q' e ih =>
    simp only [Quiver.Path.comp_cons, Quiver.Path.vertices_cons, List.concat_eq_append]
    exact List.mem_append.mpr (Or.inl ih)

private theorem mem_vertices_comp_right {V : Type*} [Quiver V] {a b c : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} {v : V} (hv : v ∈ q.vertices) : v ∈ (p.comp q).vertices := by
  induction q with
  | nil =>
    have hvb : v = b := by simpa using hv
    subst hvb
    exact Quiver.Path.end_mem_vertices p
  | cons q' e ih =>
    rw [Quiver.Path.comp_cons, Quiver.Path.vertices_cons, List.concat_eq_append]
    rw [Quiver.Path.vertices_cons, List.concat_eq_append] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact List.mem_append.mpr (Or.inl (ih hv))
    · rw [List.mem_singleton] at hv
      subst hv
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- In a tree, the geodesic segment between two vertices is convex: any reduced path between two
vertices of `reducedSpan a b` has all its vertices in `reducedSpan a b`. -/
theorem isConvexSet_reducedSpan {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} (a b : V) :
    Work.ORBassSerre.IsConvexSet (Work.ORBassSerre.reducedSpan a b) := by
  -- Write everything in terms of the vertices of the geodesic `g := hT.geodesic a b`.
  intro x hx y hy p hp v hv
  rw [hT.reducedSpan_eq] at hx hy ⊢
  -- Split `g` at `x` and at `y`.
  obtain ⟨A, B, hAB⟩ := (hT.geodesic a b).exists_eq_comp_of_mem_vertices hx
  obtain ⟨A', B', hAB'⟩ := (hT.geodesic a b).exists_eq_comp_of_mem_vertices hy
  have hg : (hT.geodesic a b).IsReduced := hT.geodesic_isReduced a b
  have hA : A.IsReduced := by
    have h := hg; rw [hAB] at h; exact Quiver.Path.IsReduced.of_comp h
  have hA' : A'.IsReduced := by
    have h := hg; rw [hAB'] at h; exact Quiver.Path.IsReduced.of_comp h
  have hcomp : A.comp B = A'.comp B' := hAB.symm.trans hAB'
  -- The two splitting points are linearly ordered along `g`.
  rcases Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq hcomp with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- `A' = A.comp r`, with `r : Path x y` the piece of `g` from `x` to `y`.
    -- By uniqueness of reduced paths, `p = r`, and `r` is a piece of `g`.
    have hrr : r.IsReduced := by
      have h := hA'; rw [hr] at h; exact isReduced_of_comp_right h
    have hp_eq : p = r := Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree hT hp hrr
    have hgdecomp : hT.geodesic a b = A.comp (r.comp B') := by
      rw [hAB', hr, Quiver.Path.comp_assoc]
    rw [hp_eq] at hv
    rw [hgdecomp]
    exact mem_vertices_comp_right (mem_vertices_comp_left hv)
  · -- `A = A'.comp r`, with `r : Path y x` the piece of `g` from `y` to `x`.
    -- Then `p = r.reverse`, and `r` is a piece of `g` too.
    have hrr : r.IsReduced := by
      have h := hA; rw [hr] at h; exact isReduced_of_comp_right h
    have hpr : p.reverse = r :=
      Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree hT hp.reverse hrr
    have hp_eq : p = r.reverse := by
      have h := congrArg Quiver.Path.reverse hpr
      rwa [Quiver.Path.reverse_reverse] at h
    rw [hp_eq] at hv
    have hv' : v ∈ r.vertices := (mem_vertices_reverse_iff r).mp hv
    have hA_mem : v ∈ A.vertices := by
      have h := mem_vertices_comp_right (p := A') (q := r) hv'
      rwa [← hr] at h
    rw [hAB]
    exact mem_vertices_comp_left hA_mem

end Work.ORBassSerre.Tree.Seg
