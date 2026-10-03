/-
# The decoding prefunctor of a skeleton is injective on total arrows

`Skeleton.lean` exhibits the encoding `S.enc : V ⥤q S.Vx` and the decoding `S.dec : S.Vx ⥤q V` of a
skeleton, together with the fact `Skel.dec_totalMap_enc_totalMap` that the decoding of the encoding
of an arrow of `V` is that arrow.

Here we prove the injectivity half of the statement that `S.enc` and `S.dec` are mutually inverse:
`S.dec` is injective on objects (`Skel.decObj_injective`) and on arrows (`Skel.dec_map_injective`),
and we record the general fact that a prefunctor with these two properties induces an injective map
on the *total space* `Quiver.Total` of arrows (`PrefunctorAux.totalMap_injective_of'`).
-/
import Mathlib
import Submission.Work.Case1.Skeleton

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v w

namespace Work.Case1

namespace PrefunctorAux

/-- Arrows which are equal as elements of `Quiver.Total` have `HEq`-equal underlying homs. -/
private theorem total_hom_heq_of_eq' {U : Type w} [Quiver U] {x y : Quiver.Total U} (h : x = y) :
    HEq x.hom y.hom := by
  cases h
  rfl

/-- A prefunctor commutes with the casting of an arrow along vertex equalities. -/
private theorem map_cast' {U : Type w} {X : Type u} [Quiver U] [Quiver X] (F : U ⥤q X)
    {a b a' b' : U} (e : a ⟶ b) (hu : a = a') (hv : b = b') :
    F.map (e.cast hu hv) = (F.map e).cast (congrArg F.obj hu) (congrArg F.obj hv) := by
  cases hu
  cases hv
  rfl

/-- A prefunctor which is injective on objects and on every hom set induces an injective map on the
total space of arrows. -/
private theorem totalMap_injective_of' {U : Type w} {X : Type u} [Quiver U] [Quiver X]
    (F : U ⥤q X) (hinj_obj : Function.Injective F.obj)
    (hinj : ∀ ⦃a b : U⦄, Function.Injective (fun e : a ⟶ b => F.map e)) :
    Function.Injective (totalMap F) := by
  intro e e' h
  have hL : e.left = e'.left := hinj_obj (congrArg Quiver.Total.left h)
  have hR : e.right = e'.right := hinj_obj (congrArg Quiver.Total.right h)
  have hhom : HEq (F.map e.hom) (F.map e'.hom) := total_hom_heq_of_eq' h
  refine Quiver.Total.ext hL hR ?_
  have hmap : F.map (e.hom.cast hL hR) = F.map e'.hom := by
    rw [map_cast']
    exact (Quiver.Hom.cast_eq_iff_heq (congrArg F.obj hL) (congrArg F.obj hR)
      (F.map e.hom) (F.map e'.hom)).2 hhom
  have heq : e.hom.cast hL hR = e'.hom := hinj hmap
  exact (Quiver.Hom.cast_eq_iff_heq hL hR e.hom e'.hom).1 heq

end PrefunctorAux

theorem dec_totalMap_injective {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] {W : Type u}
    (S : Work.Case1.Skel V W) :
    Function.Injective (Work.Case1.PrefunctorAux.totalMap S.dec) :=
  PrefunctorAux.totalMap_injective_of' S.dec S.decObj_injective (fun _ _ => S.dec_map_injective)

end Work.Case1
