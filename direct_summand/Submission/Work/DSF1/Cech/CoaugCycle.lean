import Mathlib
import Submission.Work.DSF1.Cech.UnitCaseSetup

/-!
# The augmented Čech complex is a complex

For a presheaf of `S`-modules `Q` on the opens of a scheme `X` and a family of opens
`U : ι → X.Opens`, the coaugmentation `coaug U Q : Q(⊤) ⟶ Č⁰` is killed by the first
differential: `coaug ≫ d 0 1 = 0`.  This is what makes the augmented complex
`0 ⟶ Q(⊤) ⟶ Č⁰ ⟶ Č¹ ⟶ …` a complex.

The proof is a componentwise computation.  On the `y`-th component (`y : Fin 2 → ι`, a
pair of indices) the differential `d 0 1` is the alternating sum of the two cofaces, and
after composing with `coaug` both terms become the restriction `Q(⊤) ⟶ Q(U (y 0) ⊓ U (y 1))`
(morphisms into `⊤` in `X.Opens` are unique), so the two terms cancel.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {X : Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}

/-- **Component formula for the Čech differential.**  The `x`-th component of the
differential `d n (n+1)` of the Čech complex is the alternating sum of the components of
the individual cofaces.

This is the same statement as `Work.DSF1.Cech.cechComplexFunctor_d_π`, but with the
universe parameters of the target category left free, so that it can be applied to
`ModuleCat S` (whose hom-universe is *not* its object-universe). -/
lemma cech_d_comp_π (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat S) (n : ℕ)
    (x : ((E U).obj (op ⦋n+1⦌)).I) :
    ((cechComplexFunctor U).obj Q).d n (n+1) ≫
        Pi.π (fun y => Q.obj (op (Eobj U (n+1) y))) x =
      ∑ a : Fin (n+2), (-1:ℤ)^(a:ℕ) •
        (Pi.π (fun y => Q.obj (op (Eobj U n y))) (((E U).map (SimplexCategory.δ a).op).f x) ≫
          Q.map (((E U).map (SimplexCategory.δ a).op).φ x).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

/-- The composite of the coaugmentation with the `a`-th coface, projected to the `y`-th
component, is the restriction map `Q(⊤) ⟶ Q (E 1 y)`. -/
lemma coaug_delta_comp_π (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat S)
    (a : Fin 2) (y : ((E U).obj (op ⦋1⦌)).I) :
    (coaug U Q ≫ (Cosimplicial U Q).δ a) ≫
        Pi.π (fun z => Q.obj (op (Eobj U 1 z))) y =
      Q.map (homOfLE (le_top : Eobj U 1 y ≤ ⊤)).op := by
  rw [Category.assoc, cech_delta_comp_π U Q 0 a y, ← Category.assoc]
  rw [show coaug U Q ≫
        Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ a).op).f y) =
      Q.map (homOfLE le_top).op from Pi.lift_comp_π _ _]
  rw [← Q.map_comp]
  congr 1

lemma CoaugCycle {X : AlgebraicGeometry.Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}
    (U : ι → X.Opens) (Q : CategoryTheory.Functor (X.Opensᵒᵖ) (ModuleCat S)) :
    CategoryTheory.CategoryStruct.comp (Work.DSF1.Cech.coaug U Q)
      (((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1) = 0 := by
  refine Pi.hom_ext _ _ (fun y => ?_)
  simp only [zero_comp]
  change (coaug U Q ≫ ((cechComplexFunctor U).obj Q).d 0 1) ≫
      Pi.π (fun z => Q.obj (op (Eobj U 1 z))) y = 0
  rw [Category.assoc]
  rw [show ((cechComplexFunctor U).obj Q).d 0 1 ≫
        Pi.π (fun z => Q.obj (op (Eobj U 1 z))) y =
      ∑ a : Fin 2, (-1:ℤ)^(a:ℕ) •
        (Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ a).op).f y) ≫
          Q.map (((E U).map (SimplexCategory.δ a).op).φ y).op) from cech_d_comp_π U Q 0 y]
  rw [Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (fun a _ => Preadditive.comp_zsmul _ _ _)]
  have hterm : ∀ a : Fin 2,
      (coaug U Q ≫
          (Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ a).op).f y) ≫
            Q.map (((E U).map (SimplexCategory.δ a).op).φ y).op)) =
        Q.map (homOfLE (le_top : Eobj U 1 y ≤ ⊤)).op := by
    intro a
    rw [← Category.assoc]
    rw [show coaug U Q ≫
          Pi.π (fun z => Q.obj (op (Eobj U 0 z))) (((E U).map (SimplexCategory.δ a).op).f y) =
        Q.map (homOfLE le_top).op from Pi.lift_comp_π _ _]
    rw [← Q.map_comp]
    congr 1
  simp only [hterm]
  rw [Fin.sum_univ_two]
  simp

end Work.DSF1.Cech
