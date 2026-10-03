/-
# The action of a prefunctor on paths

Generic lemmas about `Prefunctor.mapPath` for a prefunctor `F : U ⥤q W` which preserves reversal
(`F.MapReverse`): functoriality with respect to `comp`, `pmul`, `red`, `compPower`; preservation of
length, of the vertex list and of the arrow list; and preservation/reflection of reducedness.

These are the path-level facts used by the "small model" construction
(`Submission/Work/Case1/Skeleton.lean`, `Submission/Work/Case1/smallModel.lean`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORBassSerre.Path.Map.reducesTo_mapPath
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v w

namespace Work.Case1

open Quiver

namespace PrefunctorAux

variable {U : Type u} {W : Type w} [Quiver U] [Quiver W]

/-- The action of a prefunctor on the total space of arrows. -/
def totalMap (F : U ⥤q W) (e : Quiver.Total U) : Quiver.Total W :=
  Quiver.Total.mk (F.obj e.left) (F.obj e.right) (F.map e.hom)

@[simp] theorem totalMap_left (F : U ⥤q W) (e : Quiver.Total U) :
    (totalMap F e).left = F.obj e.left := rfl

@[simp] theorem totalMap_right (F : U ⥤q W) (e : Quiver.Total U) :
    (totalMap F e).right = F.obj e.right := rfl

@[simp] theorem totalMap_hom (F : U ⥤q W) (e : Quiver.Total U) :
    (totalMap F e).hom = F.map e.hom := rfl

/-- `mapPath` commutes with the casting of a path along equalities of its endpoints.  (The same
lemma exists in this repository as `Work.ORBassSerre.PathAux.mapPath_cast`.) -/
theorem mapPath_cast (F : U ⥤q W) {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a')
    (h2 : b = b') :
    F.mapPath (p.cast h1 h2) =
      (F.mapPath p).cast (congrArg F.obj h1) (congrArg F.obj h2) := by
  subst h1; subst h2; simp

theorem mapPath_length (F : U ⥤q W) {a b : U} (p : Quiver.Path a b) :
    (F.mapPath p).length = p.length := by
  induction p with
  | nil => rw [Prefunctor.mapPath_nil]; rfl
  | cons p e ih => rw [Prefunctor.mapPath_cons, Quiver.Path.length_cons, Quiver.Path.length_cons, ih]

theorem mapPath_vertices (F : U ⥤q W) {a b : U} (p : Quiver.Path a b) :
    (F.mapPath p).vertices = p.vertices.map F.obj := by
  induction p with
  | nil => rw [Prefunctor.mapPath_nil]; rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Quiver.Path.vertices_cons, ih, Quiver.Path.vertices_cons,
        List.map_concat]

theorem mapPath_arrowList (F : U ⥤q W) {a b : U} (p : Quiver.Path a b) :
    (F.mapPath p).arrowList = p.arrowList.map (totalMap F) := by
  induction p with
  | nil => rw [Prefunctor.mapPath_nil]; rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Quiver.Path.arrowList_cons, ih, Quiver.Path.arrowList_cons,
        List.map_append]
      rfl

theorem mapPath_compPower (F : U ⥤q W) {a : U} (q : Quiver.Path a a) (m : ℕ) :
    F.mapPath (q.compPower m) = (F.mapPath q).compPower m := by
  induction m with
  | zero =>
      rw [Quiver.Path.compPower_zero, Quiver.Path.compPower_zero, Prefunctor.mapPath_nil]
  | succ m ih =>
      rw [Quiver.Path.compPower_succ, Prefunctor.mapPath_comp, ih, Quiver.Path.compPower_succ]

section Reverse

variable [Quiver.HasInvolutiveReverse U] [Quiver.HasInvolutiveReverse W]

/-- `totalMap` commutes with reversal. -/
theorem totalMap_totalReverse (F : U ⥤q W) [F.MapReverse] (e : Quiver.Total U) :
    totalMap F (Quiver.totalReverse e) = Quiver.totalReverse (totalMap F e) := by
  refine Quiver.Total.ext rfl rfl ?_
  show HEq (F.map (Quiver.totalReverse e).hom) (Quiver.reverse (F.map e.hom))
  rw [Quiver.totalReverse_hom]
  exact heq_of_eq (Prefunctor.map_reverse F e.hom)

theorem mapPath_reverse (F : U ⥤q W) [F.MapReverse] {a b : U} (p : Quiver.Path a b) :
    F.mapPath p.reverse = (F.mapPath p).reverse :=
  Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse F p

/-- A backtrack of `p` gives a backtrack of `F.mapPath p`. -/
theorem not_isReduced_mapPath (F : U ⥤q W) [F.MapReverse] {a b : U} (p : Quiver.Path a b)
    (hp : ¬ p.IsReduced) : ¬ (F.mapPath p).IsReduced := by
  intro hred
  apply hp
  intro q hq
  exact hred (F.mapPath q) (Work.ORBassSerre.Path.Map.deleteBacktrack_mapPath F hq)

/-- A prefunctor injective on objects and on arrows preserves reducedness. -/
theorem mapPath_isReduced (F : U ⥤q W) [F.MapReverse] (hinj_obj : Function.Injective F.obj)
    (hinj : ∀ ⦃a b : U⦄, Function.Injective (fun e : a ⟶ b => F.map e))
    {a b : U} {p : Quiver.Path a b} (hp : p.IsReduced) : (F.mapPath p).IsReduced :=
  Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced F hinj_obj hinj hp

/-- Reducedness is preserved and reflected by a prefunctor injective on objects and on arrows. -/
theorem mapPath_isReduced_iff (F : U ⥤q W) [F.MapReverse]
    (hinj_obj : Function.Injective F.obj)
    (hinj : ∀ ⦃a b : U⦄, Function.Injective (fun e : a ⟶ b => F.map e))
    {a b : U} (p : Quiver.Path a b) :
    (F.mapPath p).IsReduced ↔ p.IsReduced :=
  ⟨fun h => by
    by_contra h'
    exact not_isReduced_mapPath F p h' h,
   fun h => mapPath_isReduced F hinj_obj hinj h⟩

/-- The reduced form of the image of a path is the image of its reduced form. -/
theorem mapPath_red (F : U ⥤q W) [F.MapReverse]
    (hinj_obj : Function.Injective F.obj)
    (hinj : ∀ ⦃a b : U⦄, Function.Injective (fun e : a ⟶ b => F.map e))
    {a b : U} (p : Quiver.Path a b) :
    F.mapPath (Work.ORLocInd.Howie.red p) = Work.ORLocInd.Howie.red (F.mapPath p) :=
  (Work.ORLocInd.Howie.red_eq_of_reducesTo_isReduced
      (Work.ORBassSerre.Path.Map.reducesTo_mapPath F
        (Work.ORLocInd.Howie.reducesTo_red p))
      (mapPath_isReduced F hinj_obj hinj (Work.ORLocInd.Howie.isReduced_red p))).symm

/-- `mapPath` is compatible with the free-groupoid product `pmul`. -/
theorem mapPath_pmul (F : U ⥤q W) [F.MapReverse]
    (hinj_obj : Function.Injective F.obj)
    (hinj : ∀ ⦃a b : U⦄, Function.Injective (fun e : a ⟶ b => F.map e))
    {a b c : U} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    F.mapPath (Work.ORLocInd.Howie.pmul p q) =
      Work.ORLocInd.Howie.pmul (F.mapPath p) (F.mapPath q) := by
  show F.mapPath (Work.ORLocInd.Howie.red (p.comp q)) =
    Work.ORLocInd.Howie.red ((F.mapPath p).comp (F.mapPath q))
  rw [mapPath_red F hinj_obj hinj (p.comp q), Prefunctor.mapPath_comp]

end Reverse

end PrefunctorAux

end Work.Case1
