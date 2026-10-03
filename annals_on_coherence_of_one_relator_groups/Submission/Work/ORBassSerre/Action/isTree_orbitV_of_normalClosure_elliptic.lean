import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientReverse
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Action.Quotient.qpath_exists_lift
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced
import Submission.Work.ORBassSerre.Path.Reduction.reducesTo_nil_comp_reverse
import Submission.Work.ORBassSerre.Path.Reduction.reducesTo_geodesic
import Submission.Work.ORBassSerre.Path.Reduction.reducesTo_of_reducesTo_of_isReduced
import Submission.Work.ORBassSerre.Path.Map.reducesTo_mapPath
import Submission.Work.ORBassSerre.Action.orbitPrefunctor_mapPath_smul_heq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w

open Work.ORBassSerre.Path.Reduction Work.ORBassSerre.Path.Map

namespace Work.ORBassSerre.PathAux

open Quiver

variable {V : Type u} [Quiver V]

theorem cast_comp {a b c a' c' : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (hu : a = a') (hw : c = c') :
    (p.comp q).cast hu hw = (p.cast hu rfl).comp (q.cast rfl hw) := by
  subst hu; subst hw; rfl

theorem cast_length {a b a' b' : V} (p : Quiver.Path a b) (hu : a = a') (hv : b = b') :
    (p.cast hu hv).length = p.length := by
  subst hu; subst hv; rfl

theorem cast_congr {a b a' b' : V} (p : Quiver.Path a b) {hu hu' : a = a'} {hv hv' : b = b'}
    (hh : hu = hu') (hh' : hv = hv') : p.cast hu hv = p.cast hu' hv' := by
  rw [hh, hh']

variable [Quiver.HasReverse V]

theorem cast_reverse {a b a' b' : V} (p : Quiver.Path a b) (hu : a = a') (hv : b = b') :
    (p.cast hu hv).reverse = (p.reverse).cast hv hu := by
  subst hu; subst hv; rfl

theorem cast_reducesTo {a b a' b' : V} {p q : Quiver.Path a b} (h : p.ReducesTo q)
    (hu : a = a') (hv : b = b') : (p.cast hu hv).ReducesTo (q.cast hu hv) := by
  subst hu; subst hv; simpa using h

theorem cast_isReduced {a b a' b' : V} {p : Quiver.Path a b} (h : p.IsReduced)
    (hu : a = a') (hv : b = b') : (p.cast hu hv).IsReduced := by
  subst hu; subst hv; simpa using h

theorem reducesTo_comp_left {a b c : V} {q q' : Quiver.Path b c} (h : q.ReducesTo q')
    (r : Quiver.Path a b) : (r.comp q).ReducesTo (r.comp q') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (Quiver.Path.DeleteBacktrack.comp_left hstep r)

theorem reducesTo_comp {a b c : V} {p p' : Quiver.Path a b} {q q' : Quiver.Path b c}
    (hp : p.ReducesTo p') (hq : q.ReducesTo q') : (p.comp q).ReducesTo (p'.comp q') :=
  (Quiver.Path.ReducesTo.comp_right hp q).trans (reducesTo_comp_left hq p')

theorem mapPath_cast {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W) {a b a' b' : V}
    (p : Quiver.Path a b) (hu : a = a') (hv : b = b') :
    F.mapPath (p.cast hu hv) = (F.mapPath p).cast (congrArg F.obj hu) (congrArg F.obj hv) := by
  subst hu; subst hv; simp

end Work.ORBassSerre.PathAux

namespace Work.ORBassSerre.Action

open Quiver

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [GraphAction G V]

/-- The trivial path in the quotient between two vertices whose class coincides. -/
def nilPath (X Y : orbitV G V) (h : X = Y) : Quiver.Path X Y :=
  Quiver.Path.cast rfl h (Quiver.Path.nil : Quiver.Path X X)

theorem nilPath_self (X : orbitV G V) (h : X = X) : nilPath X X h = Quiver.Path.nil := by
  rw [Subsingleton.elim h rfl, nilPath, Quiver.Path.cast_rfl_rfl]

theorem nilPath_congr {X Y : orbitV G V} (h h' : X = Y) : nilPath X Y h = nilPath X Y h' := by
  rw [Subsingleton.elim h h']

theorem nilPath_length (X Y : orbitV G V) (h : X = Y) : (nilPath X Y h).length = 0 := by
  rw [nilPath, PathAux.cast_length]
  rfl

theorem nilPath_isReduced (X Y : orbitV G V) (h : X = Y) : (nilPath X Y h).IsReduced := by
  refine Quiver.Path.IsReduced.of_length_lt_two ?_
  rw [nilPath_length]
  omega

theorem nilPath_comp (X Y Z : orbitV G V) (h : X = Y) (h' : Y = Z) :
    (nilPath X Y h).comp (nilPath Y Z h') = nilPath X Z (h.trans h') := by
  subst h
  subst h'
  simp [nilPath]

theorem nilPath_reverse (X Y : orbitV G V) (h : X = Y) :
    (nilPath X Y h).reverse = nilPath Y X h.symm := by
  subst h
  simp [nilPath]

/-- The class of `g • x` is the class of `x`. -/
theorem orbit_obj_eq_obj_smul (g : G) (x : V) : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x = (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (g • x) :=
  Quotient.sound ⟨g⁻¹, by simp⟩

theorem cast_eq_of_cast_eq {a b a' b' : V} {p : Quiver.Path a b} {q : Quiver.Path a' b'}
    {hu : a = a'} {hv : b = b'} (h : p.cast hu hv = q) : p = q.cast hu.symm hv.symm := by
  subst hu; subst hv; simpa using h

theorem cast_nil_congr {W₀ W₁ W₂ : orbitV G V} (hu : W₀ = W₁) (hv : W₀ = W₂) (hv' : W₁ = W₂) :
    (Quiver.Path.cast hu hv (Quiver.Path.nil : Quiver.Path W₀ W₀)) =
      (Quiver.Path.cast rfl hv' (Quiver.Path.nil : Quiver.Path W₁ W₁)) := by
  subst hu; subst hv
  exact congrArg (fun h => Quiver.Path.cast rfl h (Quiver.Path.nil : Quiver.Path W₀ W₀))
    (Subsingleton.elim hv' rfl).symm

theorem nilPath_cast_nil (X Y : orbitV G V) (h : X = Y) (h' : Y = X) :
    (nilPath X Y h).cast rfl h' = Quiver.Path.nil := by
  rw [nilPath, Quiver.Path.cast_cast]
  exact cast_nil_congr _ _ rfl

theorem nilPath_cast_nilPath {X Y Z : orbitV G V} (h : X = Y) (h' : Y = Z) :
    (nilPath X Y h).cast rfl h' = nilPath X Z (h.trans h') := by
  rw [nilPath, nilPath, Quiver.Path.cast_cast]

theorem nilPath_cast_start {X X' Y : orbitV G V} (h : X = X') (h' : X' = Y) :
    (nilPath X' Y h').cast h.symm rfl = nilPath X Y (h.trans h') := by
  rw [nilPath, nilPath, Quiver.Path.cast_cast]
  exact cast_nil_congr _ _ _

theorem mapPath_smulPath_cast (z : G) {a b : V} (d : Quiver.Path a b) :
    (Quiver.Path.cast (orbit_obj_eq_obj_smul (G := G) (V := V) z a).symm
      (orbit_obj_eq_obj_smul (G := G) (V := V) z b).symm
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (smulPath z d))) = (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d := by
  exact (Quiver.Path.cast_eq_iff_heq (orbit_obj_eq_obj_smul (G := G) (V := V) z a).symm
      (orbit_obj_eq_obj_smul (G := G) (V := V) z b).symm
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (smulPath z d)) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d)).2
    (orbitPrefunctor_mapPath_smul_heq (G := G) (V := V) z d)

theorem geodesic_reverse (hT : IsTree V) (a b : V) :
    (hT.geodesic a b).reverse = hT.geodesic b a :=
  hT.eq_geodesic (hT.geodesic_isReduced a b).reverse

/-- The image in the quotient of the "V-shaped" walk from `x` to `z • x` (going from `x` to a
fixed vertex `w0` of `z` and back via the translate of that path) is null-reducible. -/
theorem mapPath_vee_reducesTo {x w0 : V} (z : G) (hz : z • w0 = w0) (d : Quiver.Path x w0) :
    ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (d.comp (((smulPath z d).reverse).cast hz rfl))).ReducesTo
      (nilPath ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • x)) (orbit_obj_eq_obj_smul (G := G) (V := V) z x)) := by
  haveI : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).MapReverse := orbitPrefunctor_mapReverse (G := G) (V := V)
  let hA : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x = (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • x) := orbit_obj_eq_obj_smul (G := G) (V := V) z x
  let hB : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj w0 = (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • w0) := orbit_obj_eq_obj_smul (G := G) (V := V) z w0
  have hms : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (smulPath z d) = ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).cast hA hB :=
    cast_eq_of_cast_eq (mapPath_smulPath_cast (G := G) (V := V) z d)
  let C2 : Quiver.Path ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj w0) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • x)) :=
    ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath ((smulPath z d).reverse)).cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)
  let E2 : Quiver.Path ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj w0) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • x)) :=
    (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (smulPath z d)).reverse).cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)
  let E3 : Quiver.Path ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj w0) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • x)) :=
    ((((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).cast hA hB).reverse).cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)
  let E4 : Quiver.Path ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj w0) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (z • x)) := (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse).cast rfl hA
  have h1 : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (d.comp (((smulPath z d).reverse).cast hz rfl))
      = ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).comp C2 :=
    (Prefunctor.mapPath_comp (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) d (((smulPath z d).reverse).cast hz rfl)).trans
      (congrArg (fun p => ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).comp p)
        (PathAux.mapPath_cast (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) ((smulPath z d).reverse) hz rfl))
  have h2 : C2 = E2 :=
    congrArg (fun p => p.cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl))
      (Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) (smulPath z d))
  have h3 : E2 = E3 :=
    congrArg (fun p => p.cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl))
      (congrArg Quiver.Path.reverse hms)
  have h4 : E3 = E4 := by
    have h4a : E3 = ((((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse).cast hB hA).cast
        (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl) :=
      congrArg (fun p => p.cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl))
        (PathAux.cast_reverse ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d) hA hB)
    have h4b : ((((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse).cast hB hA).cast
        (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)
        = (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse).cast (hB.trans (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz))
            (hA.trans (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)) :=
      Quiver.Path.cast_cast (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse) hB hA (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz)
        (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)
    have h4c : (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse).cast (hB.trans (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz))
        (hA.trans (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)) = (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse).cast rfl hA := by
      rw [Subsingleton.elim (hB.trans (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz)) rfl,
        Subsingleton.elim (hA.trans (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl)) hA]
    exact h4a.trans (h4b.trans h4c)
  have h5 : ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).comp E4
      = ((((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).comp (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse)).cast rfl hA) := by
    have hcomp := PathAux.cast_comp ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d) (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse) rfl hA
    rw [Quiver.Path.cast_rfl_rfl] at hcomp
    exact hcomp.symm
  have hA6 : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (d.comp (((smulPath z d).reverse).cast hz rfl))
      = ((((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).comp (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).reverse)).cast rfl hA) :=
    (h1.trans (congrArg (fun p => ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d).comp p) (h2.trans (h3.trans h4)))).trans h5
  exact hA6.symm ▸ ((PathAux.cast_reducesTo (reducesTo_nil_comp_reverse ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath d)) rfl hA).trans
    (Quiver.Path.ReducesTo.refl _))

/-- **Lemma 4.1 (main ingredient).** If the acting group is generated by its elliptic elements,
then for every `g` and every vertex `x` there is a path from `x` to `g • x` whose image in the
quotient is null-reducible. -/
theorem exists_path_reducesTo_nilPath (hT : IsTree V)
    (hgen : Subgroup.closure {g : G | ∃ v : V, g • v = v} = ⊤) :
    ∀ (g : G) (x : V), ∃ p : Quiver.Path x (g • x),
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p).ReducesTo
        (nilPath ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (g • x)) (orbit_obj_eq_obj_smul (G := G) (V := V) g x)) := by
  haveI : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).MapReverse := orbitPrefunctor_mapReverse (G := G) (V := V)
  let S : Set G := {g | ∀ x : V, ∃ p : Quiver.Path x (g • x),
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p).ReducesTo
        (nilPath ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (g • x)) (orbit_obj_eq_obj_smul (G := G) (V := V) g x))}
  have hone : (1 : G) ∈ S := by
    intro x
    refine ⟨(Quiver.Path.nil : Quiver.Path x x).cast rfl (one_smul G x).symm, ?_⟩
    have h1 : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath ((Quiver.Path.nil : Quiver.Path x x).cast rfl (one_smul G x).symm)
        = nilPath ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj ((1 : G) • x))
            (orbit_obj_eq_obj_smul (G := G) (V := V) (1 : G) x) := by
      rw [PathAux.mapPath_cast, Prefunctor.mapPath_nil]
      exact nilPath_congr _ _
    rw [h1]
    exact Quiver.Path.ReducesTo.refl _
  have hmul : ∀ g h : G, g ∈ S → h ∈ S → g * h ∈ S := by
    intro g h hg hh x
    obtain ⟨p, hp⟩ := hh x
    obtain ⟨q, hq⟩ := hg (h • x)
    refine ⟨p.comp (q.cast rfl (mul_smul g h x).symm), ?_⟩
    have himg : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (p.comp (q.cast rfl (mul_smul g h x).symm))
        = ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p).comp (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath q).cast rfl
            (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (mul_smul g h x).symm)) := by
      rw [Prefunctor.mapPath_comp, PathAux.mapPath_cast]
    rw [himg]
    have hcomp := PathAux.reducesTo_comp hp
      (PathAux.cast_reducesTo hq rfl (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (mul_smul g h x).symm))
    rw [nilPath_cast_nilPath] at hcomp
    rw [nilPath_comp] at hcomp
    rw [nilPath_congr _ (orbit_obj_eq_obj_smul (G := G) (V := V) (g * h) x)] at hcomp
    exact hcomp
  have hinv : ∀ g : G, g ∈ S → g⁻¹ ∈ S := by
    intro g hg x
    obtain ⟨q, hq⟩ := hg (g⁻¹ • x)
    have hz : g • (g⁻¹ • x) = x := by rw [← mul_smul, mul_inv_cancel, one_smul]
    refine ⟨(q.cast rfl hz).reverse, ?_⟩
    have himg : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath ((q.cast rfl hz).reverse)
        = (((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath q).reverse).cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) rfl :=
      (congrArg (fun r => (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath r) (PathAux.cast_reverse q rfl hz)).trans
        ((PathAux.mapPath_cast (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) q.reverse hz rfl).trans
          (congrArg (fun r => r.cast (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj rfl))
            (Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) q)))
    rw [himg]
    have hq' := Quiver.Path.ReducesTo.reverse hq
    rw [nilPath_reverse] at hq'
    have hcast := PathAux.cast_reducesTo hq' (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz) rfl
    rw [nilPath_cast_start (X := (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x) (X' := (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (g • (g⁻¹ • x)))
      (h := (congrArg (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj hz).symm)] at hcast
    rw [nilPath_congr _ (orbit_obj_eq_obj_smul (G := G) (V := V) g⁻¹ x)] at hcast
    exact hcast
  let K : Subgroup G :=
    { carrier := S
      one_mem' := hone
      mul_mem' := fun {g h} hg hh => hmul g h hg hh
      inv_mem' := fun {g} hg => hinv g hg }
  have hEll : ∀ g : G, (∃ v : V, g • v = v) → g ∈ K := by
    intro z hz
    obtain ⟨w0, hw0⟩ := hz
    intro x
    refine ⟨(hT.geodesic x w0).comp
      (((smulPath z (hT.geodesic x w0)).reverse).cast hw0 rfl), ?_⟩
    exact mapPath_vee_reducesTo (G := G) (V := V) z hw0 (hT.geodesic x w0)
  have htop : (⊤ : Subgroup G) ≤ K := by
    rw [← hgen]
    exact (Subgroup.closure_le K).2 hEll
  intro g x
  exact htop trivial x

/-- **Lemma 4.1 (main ingredient), geodesic form.** If the acting group is generated by its
elliptic elements, then for every `g` and every vertex `x` the image in the quotient of the
geodesic from `x` to `g • x` is null-reducible. -/
theorem geodesic_reducesTo_nilPath (hT : IsTree V)
    (hgen : Subgroup.closure {g : G | ∃ v : V, g • v = v} = ⊤) (g : G) (x : V) :
    ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (hT.geodesic x (g • x))).ReducesTo
      (nilPath ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj x) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (g • x)) (orbit_obj_eq_obj_smul (G := G) (V := V) g x)) := by
  haveI : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).MapReverse := orbitPrefunctor_mapReverse (G := G) (V := V)
  obtain ⟨p, hp⟩ := exists_path_reducesTo_nilPath (G := G) (V := V) hT hgen g x
  exact reducesTo_of_reducesTo_of_isReduced (nilPath_isReduced _ _ _) hp
    (reducesTo_mapPath (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) (reducesTo_geodesic hT p))

/-- Every closed path in the quotient reduces to the trivial path. -/
theorem reducesTo_nil_of_closed (hT : IsTree V)
    (hgen : Subgroup.closure {g : G | ∃ v : V, g • v = v} = ⊤)
    (A : orbitV G V) (q : Quiver.Path A A) : q.ReducesTo Quiver.Path.nil := by
  haveI : (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).MapReverse := orbitPrefunctor_mapReverse (G := G) (V := V)
  obtain ⟨a, ha⟩ := Quotient.exists_rep A
  subst ha
  obtain ⟨b, p', hb, hp⟩ := Work.ORBassSerre.Action.Quotient.qpath_exists_lift_aux (G := G) (V := V) a (Quotient.mk'' a) q
  have hrel : MulAction.orbitRel G V b a := Quotient.exact hb
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  subst hg
  have hq : q = ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p').cast (orbitPrefunctor_obj (G := G) (V := V) a)
      ((orbitPrefunctor_obj (G := G) (V := V) (g • a)).trans hb) :=
    ((Quiver.Path.cast_eq_iff_heq (orbitPrefunctor_obj (G := G) (V := V) a)
      ((orbitPrefunctor_obj (G := G) (V := V) (g • a)).trans hb)
      ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p') q).2 hp).symm
  have hred : ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p').ReducesTo ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath (hT.geodesic a (g • a))) :=
    reducesTo_mapPath (Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)) (reducesTo_geodesic hT p')
  have hheart := geodesic_reducesTo_nilPath (G := G) (V := V) hT hgen g a
  have hcast1 := PathAux.cast_reducesTo hred (orbitPrefunctor_obj (G := G) (V := V) a)
    ((orbitPrefunctor_obj (G := G) (V := V) (g • a)).trans hb)
  have hcast2 := PathAux.cast_reducesTo hheart (orbitPrefunctor_obj (G := G) (V := V) a)
    ((orbitPrefunctor_obj (G := G) (V := V) (g • a)).trans hb)
  have hnil : (nilPath ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj a) ((Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).obj (g • a))
      (orbit_obj_eq_obj_smul (G := G) (V := V) g a)).cast
      (orbitPrefunctor_obj (G := G) (V := V) a)
      ((orbitPrefunctor_obj (G := G) (V := V) (g • a)).trans hb) = Quiver.Path.nil := by
    rw [nilPath, Quiver.Path.cast_cast]
    exact (cast_nil_congr _ _ rfl).trans (Quiver.Path.cast_rfl_rfl _)
  rw [hnil] at hcast2
  exact hq ▸ (hcast1.trans hcast2)

theorem eq_nil_of_isReduced_of_reducesTo_nil {X : orbitV G V} {p : Quiver.Path X X}
    (hp : p.IsReduced) (h : p.ReducesTo Quiver.Path.nil) : p = Quiver.Path.nil := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, hc, -⟩
  · exact h'
  · exact absurd hc (hp c)

theorem connected_orbitV (hT : IsTree V) : ∀ A B : orbitV G V, Nonempty (Quiver.Path A B) := by
  intro A B
  obtain ⟨a, rfl⟩ := Quotient.exists_rep A
  obtain ⟨b, rfl⟩ := Quotient.exists_rep B
  obtain ⟨p⟩ := hT.1 a b
  exact ⟨(orbitPrefunctor (G := G) (V := V)).mapPath p⟩

/-- A normal subgroup which is the normal closure of a set of elliptic elements is generated by
its elliptic elements. -/
theorem closure_elliptic_eq_top_of_normalClosure (N : Subgroup G) [N.Normal] (E : Set G)
    (hE : ∀ g ∈ E, ∃ v : V, g • v = v) (hgen : Subgroup.normalClosure E = N) :
    Subgroup.closure {g : N | ∃ v : V, (g : G) • v = v} = ⊤ := by
  let KN : Subgroup N := Subgroup.closure {g : N | ∃ v : V, (g : G) • v = v}
  have hconj : Group.conjugatesOfSet E ⊆ KN.map N.subtype := by
    rintro x hx
    obtain ⟨e, he, hconj⟩ := (Group.mem_conjugatesOfSet_iff).1 hx
    obtain ⟨c, hc⟩ := (isConj_iff (a := e) (b := x)).1 hconj
    subst hc
    have heN : e ∈ N := by rw [← hgen]; exact Subgroup.subset_normalClosure he
    have hxN : c * e * c⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem e heN c
    have hxell : ∃ v : V, (c * e * c⁻¹) • v = v := by
      obtain ⟨v, hv⟩ := hE e he
      refine ⟨c • v, ?_⟩
      simp only [mul_smul, inv_smul_smul, hv]
    exact Subgroup.mem_map.2 ⟨⟨c * e * c⁻¹, hxN⟩, Subgroup.subset_closure hxell, rfl⟩
  have hle : Subgroup.normalClosure E ≤ KN.map N.subtype := by
    have h0 : Subgroup.normalClosure E = Subgroup.closure (Group.conjugatesOfSet E) := rfl
    rw [h0]
    exact (Subgroup.closure_le (KN.map N.subtype)).2 hconj
  refine le_antisymm le_top ?_
  intro n _
  have hn : (n : G) ∈ Subgroup.normalClosure E := by rw [hgen]; exact n.2
  obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.1 (hle hn)
  rwa [show k = n from Subtype.ext hkn] at hk

end Work.ORBassSerre.Action

namespace Work.ORBassSerre.Action

open Quiver

/-- JL Lemma 4.1: if a normal subgroup `N` of the automorphism group of a tree is generated by
elements which each fix a vertex, then the quotient graph `V/N` is again a tree. -/
theorem isTree_orbitV_of_normalClosure_elliptic {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) (N : Subgroup G) [N.Normal]
    (E : Set G) (hE : ∀ g ∈ E, ∃ v : V, g • v = v) (hgen : Subgroup.normalClosure E = N) :
    Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV N V) := by
  have hgen' : Subgroup.closure {g : N | ∃ v : V, (g : G) • v = v} = ⊤ :=
    closure_elliptic_eq_top_of_normalClosure (G := G) (V := V) N E hE hgen
  refine ⟨?_, ?_⟩
  · intro A B
    exact connected_orbitV (G := N) (V := V) hT A B
  · intro A p hp
    exact eq_nil_of_isReduced_of_reducesTo_nil (G := N) (V := V) hp
      (reducesTo_nil_of_closed (G := N) (V := V) hT hgen' A p)

end Work.ORBassSerre.Action
