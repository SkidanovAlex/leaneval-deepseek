import Mathlib
import Submission.Work.ORBassSerre.Tree.Seg.smul_reducedSpan
import Submission.Work.ORBassSerre.Tree.Geodesic.mem_geodesic_length_eq

/-!
# The fixed-point set of a graph automorphism of a tree is convex

If `g` acts on a tree `V` as a graph automorphism and fixes the vertices `v` and `w`, then it
fixes every vertex of the geodesic segment between `v` and `w`.  The proof is the classical
one: translating the geodesic `v ↝ u` by `g` gives a reduced path from `v` to `g • u`, hence
the geodesic from `v` to `g • u`, and this translation does not change the length.  So `u` and
`g • u` are two vertices of the geodesic `v ↝ w` at the same distance from `v`, and on a tree
the distance from `v` along the geodesic determines the vertex
(`Work.ORBassSerre.Tree.Geodesic.mem_geodesic_length_eq`).
-/

namespace Work.ORBassSerre.Tree.Seg

open Quiver

universe u

/-- Translating a path does not change its length. -/
private theorem smulPath_length {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (g : G) {a b : V} (p : Quiver.Path a b) :
    (Work.ORBassSerre.smulPath g p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [Work.ORBassSerre.smulPath_cons, ih]

/-- Changing the endpoints of a path along equalities does not change its length. -/
private theorem length_cast {V : Type u} [Quiver V] {a b a' b' : V} (p : Quiver.Path a b)
    (hu : a = a') (hv : b = b') : (p.cast hu hv).length = p.length := by
  subst hu
  subst hv
  rfl

/-- Changing the endpoints of a reduced path along equalities keeps it reduced. -/
private theorem isReduced_cast {V : Type u} [Quiver V] [Quiver.HasReverse V] {a b a' b' : V}
    {p : Quiver.Path a b} (hp : p.IsReduced) (hu : a = a') (hv : b = b') :
    (p.cast hu hv).IsReduced := by
  subst hu
  subst hv
  exact hp

/-- If `g` fixes `v`, then translating the geodesic from `v` to `u` by `g` produces the geodesic
from `v` to `g • u`; in particular the two geodesics have the same length. -/
private theorem geodesic_length_smul {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) {g : G} {v u : V} (hv : g • v = v) :
    (hT.geodesic v (g • u)).length = (hT.geodesic v u).length := by
  have hred : (Work.ORBassSerre.smulPath g (hT.geodesic v u)).IsReduced :=
    smulPath_isReduced g (hT.geodesic_isReduced v u)
  have hred' : ((Work.ORBassSerre.smulPath g (hT.geodesic v u)).cast hv rfl).IsReduced :=
    isReduced_cast hred hv rfl
  have heq : (Work.ORBassSerre.smulPath g (hT.geodesic v u)).cast hv rfl =
      hT.geodesic v (g • u) :=
    hT.eq_geodesic hred'
  have hlen := congrArg Quiver.Path.length heq
  rw [length_cast, smulPath_length] at hlen
  exact hlen.symm

theorem smul_eq_self_of_mem_reducedSpan {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) {g : G} {v w u : V}
    (hv : g • v = v) (hw : g • w = w)
    (hu : u ∈ Work.ORBassSerre.reducedSpan v w) : g • u = u := by
  -- `u` lies on the geodesic from `v` to `w`.
  have hu_geo : u ∈ (hT.geodesic v w).vertices := (hT.reducedSpan_eq v w).le hu
  -- so does `g • u`, because `g` maps the geodesic `v ↝ w` to the geodesic `g • v ↝ g • w`.
  have hgu_mem : g • u ∈ Work.ORBassSerre.reducedSpan v w := by
    have h1 : g • u ∈ Work.ORBassSerre.reducedSpan (g • v) (g • w) :=
      smul_mem_reducedSpan (G := G) (V := V) g hu
    rwa [hv, hw] at h1
  have hgu_geo : g • u ∈ (hT.geodesic v w).vertices := (hT.reducedSpan_eq v w).le hgu_mem
  -- Both are at the same distance from `v`: the geodesic `v ↝ g • u` is the translate of the
  -- geodesic `v ↝ u` and hence has the same length.
  have hlen : (hT.geodesic v u).length = (hT.geodesic v (g • u)).length :=
    (geodesic_length_smul (G := G) (V := V) hT hv).symm
  exact (Work.ORBassSerre.Tree.Geodesic.mem_geodesic_length_eq
    (hT := hT) (z := v) (b := w) (x := u) (y := g • u) hu_geo hgu_geo hlen).symm

end Work.ORBassSerre.Tree.Seg
