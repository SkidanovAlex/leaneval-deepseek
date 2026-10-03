import Mathlib
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced
import Submission.Work.ORBassSerre.Action.Quotient.qpath_exists_lift

set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Tree.Seg

open Quiver

section Helpers

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- Translating an arrow by `g` intertwines reversal: the translate of the reverse is the reverse
of the translate. -/
theorem smulArrow_reverse (g : G) {a b : V} (e : a ⟶ b) :
    Work.ORBassSerre.GraphAction.smulArrow g (Quiver.reverse e) =
      Quiver.reverse (Work.ORBassSerre.GraphAction.smulArrow g e) := by
  have h1 : Quiver.Total.mk (g • b) (g • a)
      (Work.ORBassSerre.GraphAction.smulArrow g (Quiver.reverse e)) =
      g • (Quiver.Total.mk a b e).reverse :=
    Work.ORBassSerre.Action.Quotient.total_mk_smulArrow (G := G) (V := V) g
      (Quiver.Total.mk b a (Quiver.reverse e))
  have h2 : Quiver.Total.mk (g • a) (g • b)
      (Work.ORBassSerre.GraphAction.smulArrow g e) = g • Quiver.Total.mk a b e :=
    Work.ORBassSerre.Action.Quotient.total_mk_smulArrow (G := G) (V := V) g
      (Quiver.Total.mk a b e)
  have h3 : Quiver.Total.mk (g • b) (g • a)
      (Work.ORBassSerre.GraphAction.smulArrow g (Quiver.reverse e)) =
      Quiver.Total.mk (g • b) (g • a)
        (Quiver.reverse (Work.ORBassSerre.GraphAction.smulArrow g e)) := by
    rw [h1, Work.ORBassSerre.GraphAction.smul_reverse_apply, ← h2, Quiver.Total.reverse_mk]
  exact eq_of_heq (Quiver.Total.ext_iff.mp h3).2.2

/-- The action prefunctor of `g` preserves reversal. -/
theorem actionPrefunctor_mapReverse (g : G) :
    (Work.ORBassSerre.actionPrefunctor (V := V) g).MapReverse :=
  ⟨fun e => smulArrow_reverse (G := G) (V := V) g e⟩

/-- The action of `g` on vertices is injective. -/
theorem injective_smul_obj (g : G) : Function.Injective (fun v : V => g • v) := by
  intro a b h
  simpa using congrArg (fun w => g⁻¹ • w) h

/-- Translating an arrow by `g` is injective. -/
theorem smulArrow_injective (g : G) {a b : V} :
    Function.Injective (fun e : a ⟶ b => Work.ORBassSerre.GraphAction.smulArrow g e) := by
  intro e e' h
  change Work.ORBassSerre.GraphAction.smulArrow g e =
    Work.ORBassSerre.GraphAction.smulArrow g e' at h
  have h1 : Quiver.Total.mk (g • a) (g • b)
      (Work.ORBassSerre.GraphAction.smulArrow g e) = g • Quiver.Total.mk a b e :=
    Work.ORBassSerre.Action.Quotient.total_mk_smulArrow (G := G) (V := V) g
      (Quiver.Total.mk a b e)
  have h2 : Quiver.Total.mk (g • a) (g • b)
      (Work.ORBassSerre.GraphAction.smulArrow g e') = g • Quiver.Total.mk a b e' :=
    Work.ORBassSerre.Action.Quotient.total_mk_smulArrow (G := G) (V := V) g
      (Quiver.Total.mk a b e')
  have htot : g • Quiver.Total.mk a b e = g • Quiver.Total.mk a b e' := by
    rw [← h1, ← h2, h]
  have htot' : Quiver.Total.mk a b e = Quiver.Total.mk a b e' := by
    have := congrArg (fun t => g⁻¹ • t) htot
    simpa using this
  exact eq_of_heq (Quiver.Total.ext_iff.mp htot').2.2

/-- The vertices of the translate of a path are the translates of its vertices. -/
theorem smulPath_vertices (g : G) {a b : V} (p : Quiver.Path a b) :
    (Work.ORBassSerre.smulPath g p).vertices = p.vertices.map (fun w => g • w) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Work.ORBassSerre.smulPath_cons, Quiver.Path.vertices_cons, ih,
      List.map_concat]

/-- Translating a reduced path by a graph automorphism yields a reduced path. -/
theorem smulPath_isReduced (g : G) {a b : V} {p : Quiver.Path a b} (hp : p.IsReduced) :
    (Work.ORBassSerre.smulPath g p).IsReduced := by
  haveI := actionPrefunctor_mapReverse (G := G) (V := V) g
  exact Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced
    (Work.ORBassSerre.actionPrefunctor (V := V) g)
    (injective_smul_obj (G := G) (V := V) g)
    (fun a b => smulArrow_injective (G := G) (V := V) g) hp

/-- The translate of a vertex lying on the geodesic segment from `x` to `y` lies on the geodesic
segment from `g • x` to `g • y`. -/
theorem smul_mem_reducedSpan (g : G) {x y v : V}
    (hv : v ∈ Work.ORBassSerre.reducedSpan x y) :
    g • v ∈ Work.ORBassSerre.reducedSpan (g • x) (g • y) := by
  rw [Work.ORBassSerre.mem_reducedSpan_iff] at hv ⊢
  obtain ⟨p, hp, hv⟩ := hv
  exact ⟨Work.ORBassSerre.smulPath g p, smulPath_isReduced g hp, by
    rw [smulPath_vertices]
    exact List.mem_map.mpr ⟨v, hv, rfl⟩⟩

end Helpers

/-- The action of a group of graph automorphisms carries the geodesic segment from `x` to `y` to
the geodesic segment from `g • x` to `g • y`. -/
theorem smul_reducedSpan {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (g : G) (x y v : V) :
    v ∈ Work.ORBassSerre.reducedSpan (g • x) (g • y) ↔
      g⁻¹ • v ∈ Work.ORBassSerre.reducedSpan x y := by
  constructor
  · intro hv
    have := smul_mem_reducedSpan (G := G) (V := V) g⁻¹ hv
    simpa only [inv_smul_smul] using this
  · intro hv
    have := smul_mem_reducedSpan (G := G) (V := V) g hv
    simpa only [smul_inv_smul] using this

end Work.ORBassSerre.Tree.Seg
