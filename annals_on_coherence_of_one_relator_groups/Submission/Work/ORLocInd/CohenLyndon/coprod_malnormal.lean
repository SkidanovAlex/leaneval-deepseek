import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.Tree
import Submission.Work.ORBassSerre.Tree.Seg.smul_reducedSpan
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORLocInd.CohenLyndon.CoprodSetup

set_option autoImplicit false

namespace Work.ORLocInd.CohenLyndon

universe u v

/-! ## Tools for the Bass--Serre tree of a free product

The lemma `coprod_malnormal` is proved through the Bass--Serre tree
`Work.ORBassSerre.CoprodTree.Vertex A B` of `A ∗ B`: the element `y = x * inl a * x⁻¹` fixes the
two vertices `vA 1` and `vA x`, and an element of a group acting on a tree which fixes two distinct
vertices fixes an edge.  For the Bass--Serre tree of `A ∗ B` the arrows are labelled by group
elements and the label of `e` and of its translate by `g` differ by the factor `g`, which forces
`g = 1`. -/

section TreeTools

variable {V : Type u} [Quiver V] [Quiver.HasReverse V]

/-- Casting a reduced path along equalities of its endpoints keeps it reduced. -/
theorem path_cast_isReduced {a b a' b' : V} {p : Quiver.Path a b} (h : p.IsReduced)
    (hu : a = a') (hv : b = b') : (p.cast hu hv).IsReduced := by
  subst hu; subst hv; simpa using h

end TreeTools

/-- The label (a group element) of an arrow of the coproduct tree is unchanged when the endpoints
of the arrow are cast along equalities. -/
theorem coprodTree_hom_cast_val {A : Type u} {B : Type v} [Group A] [Group B]
    {x y x' y' : Work.ORBassSerre.CoprodTree.Vertex A B} (hu : x = x') (hv : y = y')
    (e : x ⟶ y) : ((Quiver.Hom.cast hu hv e).1 : Monoid.Coprod A B) = e.1 := by
  subst hu; subst hv
  rw [Quiver.Hom.cast_rfl_rfl]

/-- For the Bass--Serre tree of a free product, the abstract `GraphAction.smulArrow` agrees with
the concrete arrow translation `Work.ORBassSerre.CoprodTree.smulArrow` (whose label is
`g * e.1`). -/
theorem graphAction_smulArrow_eq_coprodTree {A : Type u} {B : Type v} [Group A] [Group B]
    (g : Monoid.Coprod A B) {x y : Work.ORBassSerre.CoprodTree.Vertex A B} (e : x ⟶ y) :
    Work.ORBassSerre.GraphAction.smulArrow g e =
      Work.ORBassSerre.CoprodTree.smulArrow g e := by
  have h1 := Work.ORBassSerre.Action.Quotient.total_mk_smulArrow (G := Monoid.Coprod A B)
    (V := Work.ORBassSerre.CoprodTree.Vertex A B) g (Quiver.Total.mk x y e)
  have h2 : g • Quiver.Total.mk x y e =
      Quiver.Total.mk (g • x) (g • y) (Work.ORBassSerre.CoprodTree.smulArrow g e) := rfl
  rw [h2] at h1
  exact eq_of_heq (Quiver.Total.ext_iff.mp h1).2.2

/-- **An element of a group acting on a tree which fixes two distinct vertices fixes an edge.**
More precisely: if `p` is a reduced path of positive length from `u` to `v` and `g` fixes both
`u` and `v`, then some arrow `e` of the tree lies on the geodesic from `u` to `v` and is fixed by
`g`, in the sense that `smulArrow g e = e` up to the (necessarily equal) endpoints. -/
theorem exists_fixed_arrow_of_fixes_two {G : Type u} {V : Type v} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) {g : G} {u v : V} (hu : g • u = u) (hv : g • v = v)
    {p : Quiver.Path u v} (hp : p.IsReduced) (hlen : 0 < p.length) :
    ∃ (w : V) (e : w ⟶ v) (hw : g • w = w),
      (Work.ORBassSerre.GraphAction.smulArrow g e).cast hw hv = e := by
  have hnn : p.length ≠ 0 := by omega
  obtain ⟨w, p', e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hnn
  have hq_red : ((Work.ORBassSerre.smulPath g (p'.cons e)).cast hu hv).IsReduced :=
    path_cast_isReduced (Work.ORBassSerre.Tree.Seg.smulPath_isReduced g hp) hu hv
  have hq_eq : ((Work.ORBassSerre.smulPath g (p'.cons e)).cast hu hv) = (p'.cons e) :=
    Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree hT hq_red hp
  rw [Work.ORBassSerre.smulPath_cons, Quiver.Path.cast_cons] at hq_eq
  have hw : g • w = w := Quiver.Path.obj_eq_of_cons_eq_cons hq_eq
  have heq : ((Work.ORBassSerre.GraphAction.smulArrow g e).cast rfl hv).cast hw rfl = e :=
    Quiver.hom_cast_eq_of_cons_eq_cons hq_eq
  rw [Quiver.Hom.cast_cast] at heq
  rw [Subsingleton.elim (Eq.trans rfl hw : g • w = w) hw,
    Subsingleton.elim (Eq.trans hv rfl : g • v = v) hv] at heq
  exact ⟨w, e, hw, heq⟩

/-- **Malnormality of a free factor.**  If `a ≠ 1` is an element of the first free factor `A` of
`A ∗ B`, then any `x` conjugating `inl a` back into the first factor already lies in the first
factor.  Equivalently, `A` is malnormal in `A ∗ B`.

A proof via the Bass--Serre tree `Work.ORBassSerre.CoprodTree.Vertex A B` (the file
`Submission.Work.ORBassSerre.CoprodTree.Tree` proves that it is a tree, with
`IsTree`/geodesic/`smulPath` API available) is available: `inl a` fixes the vertex `vA 1`, and any
element fixing two distinct vertices of that tree is trivial. -/
theorem coprod_malnormal {A B : Type u} [Group A] [Group B] {a : A} (ha : a ≠ 1)
    {x : Monoid.Coprod A B}
    (hx : x * Monoid.Coprod.inl a * x⁻¹ ∈ Work.ORBassSerre.CoprodTree.SubA A B) :
    x ∈ Work.ORBassSerre.CoprodTree.SubA A B := by
  by_contra hxnot
  -- The two vertices `vA 1` and `vA x` are distinct
  have huv : Work.ORBassSerre.CoprodTree.vA (1 : Monoid.Coprod A B) ≠
      Work.ORBassSerre.CoprodTree.vA x := by
    intro h
    refine hxnot ?_
    have h' : (1 : Monoid.Coprod A B)⁻¹ * x ∈ Work.ORBassSerre.CoprodTree.SubA A B :=
      Work.ORBassSerre.CoprodTree.vA_eq_vA_iff.mp h
    simpa using h'
  -- fixed vertices
  have hfix1 : (x * Monoid.Coprod.inl a * x⁻¹) •
      Work.ORBassSerre.CoprodTree.vA (1 : Monoid.Coprod A B) =
      Work.ORBassSerre.CoprodTree.vA (1 : Monoid.Coprod A B) := by
    rw [Work.ORBassSerre.CoprodTree.smul_vA, Work.ORBassSerre.CoprodTree.vA_eq_vA_iff]
    simpa using (Work.ORBassSerre.CoprodTree.SubA A B).inv_mem hx
  have hfix2 : (x * Monoid.Coprod.inl a * x⁻¹) • Work.ORBassSerre.CoprodTree.vA x =
      Work.ORBassSerre.CoprodTree.vA x := by
    rw [Work.ORBassSerre.CoprodTree.smul_vA, Work.ORBassSerre.CoprodTree.vA_eq_vA_iff]
    have h1 : ((x * Monoid.Coprod.inl a * x⁻¹) * x)⁻¹ * x = (Monoid.Coprod.inl a)⁻¹ := by
      simp [mul_assoc]
    rw [h1]
    exact (Work.ORBassSerre.CoprodTree.SubA A B).inv_mem
      (Work.ORBassSerre.CoprodTree.inl_mem_SubA a)
  -- the geodesic between them has positive length
  have hT : Work.ORBassSerre.IsTree (Work.ORBassSerre.CoprodTree.Vertex A B) :=
    Work.ORBassSerre.CoprodTree.isTree_vertex
  have hlen : 0 < (hT.geodesic (Work.ORBassSerre.CoprodTree.vA (1 : Monoid.Coprod A B))
      (Work.ORBassSerre.CoprodTree.vA x)).length := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact huv (Quiver.Path.eq_of_length_zero _ h0)
  obtain ⟨w, e, hw, heq⟩ := exists_fixed_arrow_of_fixes_two hT hfix1 hfix2
    (hT.geodesic_isReduced _ _) hlen
  -- the arrow `e` is fixed, hence `x * inl a * x⁻¹ = 1`
  have hval : ((Work.ORBassSerre.CoprodTree.smulArrow (x * Monoid.Coprod.inl a * x⁻¹) e).1 :
      Monoid.Coprod A B) = e.1 := by
    have hcast : (Work.ORBassSerre.CoprodTree.smulArrow (x * Monoid.Coprod.inl a * x⁻¹) e).cast
        hw hfix2 = e := by
      rw [← graphAction_smulArrow_eq_coprodTree (x * Monoid.Coprod.inl a * x⁻¹) e]
      exact heq
    have h2 : ((Quiver.Hom.cast hw hfix2
        (Work.ORBassSerre.CoprodTree.smulArrow (x * Monoid.Coprod.inl a * x⁻¹) e)).1 :
        Monoid.Coprod A B) = e.1 := congrArg (fun z => z.1) hcast
    exact (coprodTree_hom_cast_val hw hfix2 _).symm.trans h2
  have hmul : (x * Monoid.Coprod.inl a * x⁻¹) * e.1 = e.1 := by
    rw [← Work.ORBassSerre.CoprodTree.smulArrow_val
      (g := x * Monoid.Coprod.inl a * x⁻¹) (e := e)]
    exact hval
  have hy1 : x * Monoid.Coprod.inl a * x⁻¹ = 1 := by
    have h := congrArg (fun z => z * e.1⁻¹) hmul
    simpa [mul_assoc] using h
  have hinl : Monoid.Coprod.inl a = (1 : Monoid.Coprod A B) := by
    have h := congrArg (fun z => x⁻¹ * z * x) hy1
    simpa [mul_assoc] using h
  exact ha (Monoid.Coprod.inl_injective (by rw [hinl, map_one]))

end Work.ORLocInd.CohenLyndon
