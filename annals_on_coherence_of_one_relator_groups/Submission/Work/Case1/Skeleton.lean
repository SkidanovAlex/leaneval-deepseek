/-
# The skeleton graph of a graph, and the small model of a datum

Given a graph `V` (a quiver with an involutive reversal) together with a bijection `fv` between
`Fin M` and the vertices of `V` and a bijection `fa` between `Fin k` and the arrows of `V`, the
*skeleton* `Skel.Vx S` is the graph in the universe `u` whose vertices are the elements of
`Fin S.M` (carried into `Type u` by `ULift`) and whose arrows are the elements of `Fin S.k` whose
source and target match.

The type `W : Type u` is a parameter of the skeleton whose role is to fix the universe `u` in which
the small graph is built (it may be taken to be `ULift (Fin S.M)`; it occurs in no other way).

There are two mutually inverse (up to casts) prefunctors

* `Skel.enc S : V ⥤q Skel.Vx S`, the encoding, and
* `Skel.dec S : Skel.Vx S ⥤q V`, the decoding,

which are injective on objects and on arrows and preserve reversal, so that all the path-level
notions (reducedness, `red`, `pmul`, `compPower`, `arrowList`, ...) transfer by
`Submission/Work/Case1/PrefunctorAux.lean`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.Case1.CastPath
import Submission.Work.Case1.PrefunctorAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

namespace Work.Case1

open Quiver

/-- A *skeleton* of a graph: an indexing of its vertices and an indexing of its arrows, together
with a type `W : Type u` whose universe is the universe in which the skeleton graph is built. -/
structure Skel (V : Type v) [Quiver V] [Quiver.HasInvolutiveReverse V] (W : Type u) where
  /-- the number of vertices -/
  M : ℕ
  /-- the vertices of `V`, indexed by `Fin M` -/
  fv : Fin M ≃ V
  /-- the number of arrows -/
  k : ℕ
  /-- the arrows of `V`, indexed by `Fin k` -/
  fa : Fin k ≃ Quiver.Total V

namespace Skel

noncomputable section

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] {W : Type u}

/-- The vertex type of the small graph. -/
abbrev Vx (S : Skel V W) : Type u := ULift.{u,0} (Fin S.M)

/-- The image of a vertex of `V` in the small graph. -/
abbrev encObj (S : Skel V W) (x : V) : S.Vx := ULift.up (S.fv.symm x)

/-- The image of a vertex of the small graph in `V`. -/
abbrev decObj (S : Skel V W) (p : S.Vx) : V := S.fv p.down

theorem decObj_encObj (S : Skel V W) (x : V) : S.decObj (S.encObj x) = x :=
  Equiv.apply_symm_apply S.fv x

theorem encObj_decObj (S : Skel V W) (p : S.Vx) : S.encObj (S.decObj p) = p :=
  ULift.ext (Equiv.symm_apply_apply S.fv p.down)

/-- `x = S.decObj (S.encObj x)`. -/
theorem dO (S : Skel V W) (x : V) : x = S.decObj (S.encObj x) := (decObj_encObj S x).symm

/-- `p = S.encObj (S.decObj p)`. -/
theorem uO (S : Skel V W) (p : S.Vx) : p = S.encObj (S.decObj p) := (encObj_decObj S p).symm

theorem encObj_injective (S : Skel V W) : Function.Injective S.encObj := fun x y h =>
  (decObj_encObj S x).symm.trans ((congrArg S.decObj h).trans (decObj_encObj S y))

theorem decObj_injective (S : Skel V W) : Function.Injective S.decObj := fun x y h =>
  (uO S x).trans ((congrArg S.encObj h).trans (uO S y).symm)

/-! ## The graph of the small model -/

/-- The source vertex of the arrow of index `i`. -/
def srcIdx (S : Skel V W) (i : Fin S.k) : Fin S.M := S.fv.symm (S.fa i).left

/-- The target vertex of the arrow of index `i`. -/
def tgtIdx (S : Skel V W) (i : Fin S.k) : Fin S.M := S.fv.symm (S.fa i).right

@[simp] theorem fv_srcIdx (S : Skel V W) (i : Fin S.k) : S.fv (S.srcIdx i) = (S.fa i).left :=
  Equiv.apply_symm_apply S.fv _

@[simp] theorem fv_tgtIdx (S : Skel V W) (i : Fin S.k) : S.fv (S.tgtIdx i) = (S.fa i).right :=
  Equiv.apply_symm_apply S.fv _

/-- The arrows of the small graph. -/
abbrev Arrow (S : Skel V W) (p q : S.Vx) : Type u :=
  ULift.{u,0} {i : Fin S.k // S.srcIdx i = p.down ∧ S.tgtIdx i = q.down}

instance instQuiverVx (S : Skel V W) : Quiver S.Vx := ⟨fun p q => S.Arrow p q⟩

/-- The index of an arrow of the small graph. -/
def arrowIdx (S : Skel V W) {p q : S.Vx} (f : S.Arrow p q) : Fin S.k := f.down.1

theorem arrow_src (S : Skel V W) {p q : S.Vx} (f : S.Arrow p q) :
    S.srcIdx (S.arrowIdx f) = p.down := f.down.2.1

theorem arrow_tgt (S : Skel V W) {p q : S.Vx} (f : S.Arrow p q) :
    S.tgtIdx (S.arrowIdx f) = q.down := f.down.2.2

theorem arrow_ext (S : Skel V W) {p q : S.Vx} {f g : S.Arrow p q}
    (h : S.arrowIdx f = S.arrowIdx g) : f = g :=
  ULift.ext (x := f) (y := g) (Subtype.ext h)

/-- The index of the reverse of the arrow of index `i`. -/
def revIdx (S : Skel V W) (i : Fin S.k) : Fin S.k := S.fa.symm (Quiver.totalReverse (S.fa i))

@[simp] theorem fa_revIdx (S : Skel V W) (i : Fin S.k) :
    S.fa (S.revIdx i) = Quiver.totalReverse (S.fa i) := Equiv.apply_symm_apply S.fa _

theorem revIdx_invol (S : Skel V W) (i : Fin S.k) : S.revIdx (S.revIdx i) = i := by
  apply S.fa.injective
  rw [fa_revIdx, fa_revIdx, Quiver.totalReverse_involutive]

theorem srcIdx_revIdx (S : Skel V W) (i : Fin S.k) : S.srcIdx (S.revIdx i) = S.tgtIdx i := by
  show S.fv.symm (S.fa (S.revIdx i)).left = S.fv.symm (S.fa i).right
  rw [fa_revIdx]
  rfl

theorem tgtIdx_revIdx (S : Skel V W) (i : Fin S.k) : S.tgtIdx (S.revIdx i) = S.srcIdx i := by
  show S.fv.symm (S.fa (S.revIdx i)).right = S.fv.symm (S.fa i).left
  rw [fa_revIdx]
  rfl

/-- The reverse of an arrow of the small graph. -/
def revArrow (S : Skel V W) {p q : S.Vx} (f : S.Arrow p q) : S.Arrow q p :=
  ULift.up ⟨S.revIdx (S.arrowIdx f),
    (srcIdx_revIdx S (S.arrowIdx f)).trans (arrow_tgt S f),
    (tgtIdx_revIdx S (S.arrowIdx f)).trans (arrow_src S f)⟩

@[simp] theorem arrowIdx_revArrow (S : Skel V W) {p q : S.Vx} (f : S.Arrow p q) :
    S.arrowIdx (S.revArrow f) = S.revIdx (S.arrowIdx f) := rfl

instance instReverseVx (S : Skel V W) : Quiver.HasInvolutiveReverse S.Vx where
  reverse' := fun {p q} f => S.revArrow f
  inv' := fun {p q} f => by
    refine ULift.ext (Subtype.ext ?_)
    show S.revIdx (S.revIdx (S.arrowIdx f)) = S.arrowIdx f
    rw [revIdx_invol]

/-! ## The encoding and decoding prefunctors -/

/-- The encoding prefunctor `V ⥤q S.Vx`. -/
abbrev enc (S : Skel V W) : V ⥤q S.Vx where
  obj x := S.encObj x
  map {a b} e := ULift.up ⟨S.fa.symm (Quiver.Total.mk a b e), by
    refine ⟨?_, ?_⟩
    · show S.srcIdx (S.fa.symm (Quiver.Total.mk a b e)) = (S.encObj a).down
      simp only [srcIdx, Equiv.apply_symm_apply, encObj, ULift.down_up]
    · show S.tgtIdx (S.fa.symm (Quiver.Total.mk a b e)) = (S.encObj b).down
      simp only [tgtIdx, Equiv.apply_symm_apply, encObj, ULift.down_up]⟩

/-- The decoding prefunctor `S.Vx ⥤q V`. -/
abbrev dec (S : Skel V W) : S.Vx ⥤q V where
  obj p := S.decObj p
  map {p q} f := (S.fa (S.arrowIdx f)).hom.cast
    ((fv_srcIdx S (S.arrowIdx f)).symm.trans (congrArg S.fv (arrow_src S f)))
    ((fv_tgtIdx S (S.arrowIdx f)).symm.trans (congrArg S.fv (arrow_tgt S f)))

@[simp] theorem enc_obj (S : Skel V W) (x : V) : S.enc.obj x = S.encObj x := rfl

@[simp] theorem dec_obj (S : Skel V W) (p : S.Vx) : S.dec.obj p = S.decObj p := rfl

theorem enc_map (S : Skel V W) {a b : V} (e : a ⟶ b) :
    S.enc.map e = ULift.up ⟨S.fa.symm (Quiver.Total.mk a b e), by
      refine ⟨?_, ?_⟩
      · show S.srcIdx (S.fa.symm (Quiver.Total.mk a b e)) = (S.encObj a).down
        simp only [srcIdx, Equiv.apply_symm_apply, encObj, ULift.down_up]
      · show S.tgtIdx (S.fa.symm (Quiver.Total.mk a b e)) = (S.encObj b).down
        simp only [tgtIdx, Equiv.apply_symm_apply, encObj, ULift.down_up]⟩ := rfl

theorem dec_map (S : Skel V W) {p q : S.Vx} (f : S.Arrow p q) :
    S.dec.map f = (S.fa (S.arrowIdx f)).hom.cast
      ((fv_srcIdx S (S.arrowIdx f)).symm.trans (congrArg S.fv (arrow_src S f)))
      ((fv_tgtIdx S (S.arrowIdx f)).symm.trans (congrArg S.fv (arrow_tgt S f))) := rfl

@[simp] theorem arrowIdx_enc_map (S : Skel V W) {a b : V} (e : a ⟶ b) :
    S.arrowIdx (S.enc.map e) = S.fa.symm (Quiver.Total.mk a b e) := rfl

/-- Two arrows of `V` with the same endpoints determine the same indexed arrow. -/
theorem totalMk_injective {a b : V} {e e' : a ⟶ b}
    (h : Quiver.Total.mk a b e = Quiver.Total.mk a b e') : e = e' := by
  cases h; rfl

/-- The homs of two equal arrows of `V` are `HEq`. -/
theorem total_hom_heq_of_eq {x y : Quiver.Total V} (h : x = y) : HEq x.hom y.hom := by
  cases h; rfl

instance enc_mapReverse (S : Skel V W) : (S.enc).MapReverse where
  map_reverse' {a b} e := by
    refine ULift.ext (Subtype.ext ?_)
    show S.fa.symm (Quiver.Total.mk b a (Quiver.reverse e)) =
      S.revIdx (S.fa.symm (Quiver.Total.mk a b e))
    apply S.fa.injective
    rw [Equiv.apply_symm_apply, fa_revIdx, Equiv.apply_symm_apply]
    rfl

theorem enc_map_injective (S : Skel V W) {a b : V} :
    Function.Injective (fun e : a ⟶ b => S.enc.map e) := by
  intro e e' h
  have h' : S.fa.symm (Quiver.Total.mk a b e) = S.fa.symm (Quiver.Total.mk a b e') := by
    have hh := congrArg S.arrowIdx h
    rw [arrowIdx_enc_map, arrowIdx_enc_map] at hh
    exact hh
  have h'' : Quiver.Total.mk a b e = Quiver.Total.mk a b e' := by
    have := congrArg S.fa h'
    simpa only [Equiv.apply_symm_apply] using this
  exact totalMk_injective h''

/-- The decoding of an arrow of the small graph is injective. -/
theorem dec_map_injective (S : Skel V W) {p q : S.Vx} :
    Function.Injective (fun f : S.Arrow p q => S.dec.map f) := by
  intro f g h
  have hXY : HEq ((S.fa (S.arrowIdx f)).hom) ((S.fa (S.arrowIdx g)).hom) :=
    (Quiver.Hom.cast_heq _ _ _).symm.trans ((heq_of_eq h).trans (Quiver.Hom.cast_heq _ _ _))
  have h1 : (S.fa (S.arrowIdx f)).left = (S.fa (S.arrowIdx g)).left :=
    ((fv_srcIdx S (S.arrowIdx f)).symm.trans (congrArg S.fv (arrow_src S f))).trans
      (((fv_srcIdx S (S.arrowIdx g)).symm.trans (congrArg S.fv (arrow_src S g))).symm)
  have h2 : (S.fa (S.arrowIdx f)).right = (S.fa (S.arrowIdx g)).right :=
    ((fv_tgtIdx S (S.arrowIdx f)).symm.trans (congrArg S.fv (arrow_tgt S f))).trans
      (((fv_tgtIdx S (S.arrowIdx g)).symm.trans (congrArg S.fv (arrow_tgt S g))).symm)
  exact S.arrow_ext (S.fa.injective (Quiver.Total.ext h1 h2 hXY))

instance dec_mapReverse (S : Skel V W) : (S.dec).MapReverse where
  map_reverse' {p q} f := by
    refine eq_of_heq ?_
    have hA1 : HEq (S.dec.map (Quiver.reverse f))
        ((S.fa (S.revIdx (S.arrowIdx f))).hom) := Quiver.Hom.cast_heq _ _ _
    have hA2 : HEq ((S.fa (S.revIdx (S.arrowIdx f))).hom)
        (Quiver.reverse ((S.fa (S.arrowIdx f)).hom)) :=
      (total_hom_heq_of_eq (fa_revIdx S (S.arrowIdx f))).trans
        (HEq.refl (Quiver.reverse ((S.fa (S.arrowIdx f)).hom)))
    have hB : HEq (Quiver.reverse (S.dec.map f))
        (Quiver.reverse ((S.fa (S.arrowIdx f)).hom)) :=
      (heq_of_eq (by rw [dec_map S f, hom_cast_reverse])).trans
        (Quiver.Hom.cast_heq _ _ _)
    exact hA1.trans (hA2.trans hB.symm)

/-- The decoding of the encoding of an arrow of `V`. -/
theorem dec_map_enc_map (S : Skel V W) {a b : V} (e : a ⟶ b) :
    S.dec.map (S.enc.map e) = Quiver.Hom.cast (dO S a) (dO S b) e := by
  refine eq_of_heq ?_
  have hX : S.fa (S.arrowIdx (S.enc.map e)) = Quiver.Total.mk a b e := by
    rw [arrowIdx_enc_map]
    exact Equiv.apply_symm_apply S.fa _
  have h1 : HEq (S.dec.map (S.enc.map e)) ((S.fa (S.arrowIdx (S.enc.map e))).hom) :=
    Quiver.Hom.cast_heq _ _ _
  have h2 : HEq ((S.fa (S.arrowIdx (S.enc.map e))).hom) e :=
    (total_hom_heq_of_eq hX).trans (HEq.refl e)
  exact h1.trans (h2.trans (Quiver.Hom.cast_heq (dO S a) (dO S b) e).symm)

/-- The decoding of the encoding of a path of `V`. -/
theorem dec_mapPath_enc_mapPath (S : Skel V W) {a b : V} (p : Quiver.Path a b) :
    S.dec.mapPath (S.enc.mapPath p) = p.cast (dO S a) (dO S b) := by
  induction p with
  | nil => rw [Prefunctor.mapPath_nil, Prefunctor.mapPath_nil, Quiver.Path.cast_nil]
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, PathCast.cast_cons, ih,
        dec_map_enc_map]

/-! ## The total maps on arrows -/

theorem dec_totalMap_enc_totalMap (S : Skel V W) (e : Quiver.Total V) :
    PrefunctorAux.totalMap S.dec (PrefunctorAux.totalMap S.enc e) = e := by
  refine Quiver.Total.ext (S.decObj_encObj e.left) (S.decObj_encObj e.right) ?_
  show HEq (S.dec.map (S.enc.map e.hom)) e.hom
  rw [dec_map_enc_map]
  exact Quiver.Hom.cast_heq (dO S e.left) (dO S e.right) e.hom

end

end Skel

end Work.Case1
