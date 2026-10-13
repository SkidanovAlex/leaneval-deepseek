import Mathlib
import Submission.Work.DSF1.Sheaf.CechAugNat

/-!
# The composite of the augmentation with the degree zero Čech differential

We prove that `cechAugNat U P ≫ cechSheafD U P 0 = 0`: the augmentation of the sheaf-level Čech
complex is a cochain map with the complex `restrL P (iSup U)` concentrated in degree `0`.

The computation is componentwise and is carried out in the "concrete" form of `CechAugNat`: at an
open `W`, the degree one term is `∏ᶜ (u : (cechN U 1).I), P ((cechN U 1).obj u ⊓ W)`, the
differential is the alternating sum of the two cofaces (`d01_fac_morph`, `SSEBasic.lean`) whose
components are the restrictions along `(cechN U 1).obj u ⊓ W ≤ (cechN U 0).obj (u ∘ δ a) ⊓ W`, and
the components of the augmentation are the restrictions along
`(cechN U 0).obj y ⊓ W ≤ iSup U ⊓ W`.  Both terms of the alternating sum are thus restrictions of a
section over `iSup U ⊓ W` along two inclusions with the same source and target, whence equal.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The degree one term of the sheaf-level Čech complex, evaluated at an open `W`. -/
noncomputable abbrev cech1 {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W : X.Opens) : AddCommGrpCat.{u} :=
  ∏ᶜ (fun u : (cechN U 1).I => P.obj (op ((cechN U 1).obj u ⊓ W)))

/-- The degree zero differential of the Čech complex, in concrete form: its `u`-th component is
the alternating sum of the two cofaces. -/
noncomputable def cechD01W {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W : X.Opens) : cech0 U P W ⟶ cech1 U P W :=
  Pi.lift (fun u : (cechN U 1).I =>
    (Pi.π (fun y : (cechN U 0).I => P.obj (op ((cechN U 0).obj y ⊓ W))) (u ∘ Fin.succAbove 0) ≫
      P.map (homOfLE (inf_le_inf_right W
        (leOfHom (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 0)).φ u)))).op)
    - (Pi.π (fun y : (cechN U 0).I => P.obj (op ((cechN U 0).obj y ⊓ W)))
        (u ∘ Fin.succAbove 1) ≫
      P.map (homOfLE (inf_le_inf_right W
        (leOfHom (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 1)).φ u)))).op))

lemma cechD01W_π {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (u : (cechN U 1).I) :
    cechD01W U P W ≫ Pi.π (fun u' : (cechN U 1).I => P.obj (op ((cechN U 1).obj u' ⊓ W))) u
      = (Pi.π (fun y : (cechN U 0).I => P.obj (op ((cechN U 0).obj y ⊓ W)))
            (u ∘ Fin.succAbove 0) ≫
          P.map (homOfLE (inf_le_inf_right W
            (leOfHom (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 0)).φ u)))).op)
        - (Pi.π (fun y : (cechN U 0).I => P.obj (op ((cechN U 0).obj y ⊓ W)))
              (u ∘ Fin.succAbove 1) ≫
          P.map (homOfLE (inf_le_inf_right W
            (leOfHom (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 1)).φ u)))).op) :=
  Pi.lift_comp_π _ _

/-- The concrete differential agrees with the differential of the sheaf-level Čech complex. -/
lemma cechD01W_eq {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) :
    cechD01W U P W = ((cechComplexFunctor U).obj (restrP P W)).d 0 1 := by
  refine Pi.hom_ext _ _ (fun u => ?_)
  rw [cechD01W_π]
  exact (d01_fac_morph U (restrP P W) u).symm

/-- A morphism into a product whose components vanish is zero. -/
lemma eq_zero_of_π_comp_eq_zero {ι' : Type u} {A : AddCommGrpCat.{u}} (G : ι' → AddCommGrpCat.{u})
    (f : A ⟶ ∏ᶜ G) (h : ∀ i, f ≫ Pi.π G i = 0) : f = 0 := by
  refine Pi.hom_ext f 0 (fun i => ?_)
  rw [zero_comp]
  exact h i

/-- **The augmentation is a cochain map.**  At an open `W`, the composite of the augmentation with
the degree zero differential vanishes. -/
lemma augW_comp_cechD01W {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) :
    augW U P W ≫ cechD01W U P W = 0 := by
  refine eq_zero_of_π_comp_eq_zero
    (fun u' : (cechN U 1).I => P.obj (op ((cechN U 1).obj u' ⊓ W))) _ (fun u => ?_)
  rw [Category.assoc, cechD01W_π, Preadditive.comp_sub, sub_eq_zero]
  rw [← Category.assoc, ← Category.assoc, augW_π, augW_π, augComp_eq, augComp_eq]
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg (fun m => P.map m) (Subsingleton.elim _ _)

/-- **The augmentation of the sheaf-level Čech complex commutes with the differentials.** -/
theorem cechAugNat_comp_cechSheafD {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    cechAugNat U P ≫ cechSheafD U P 0 = 0 := by
  refine NatTrans.ext' (funext (fun W => ?_))
  show augW U P W.unop ≫ ((cechComplexFunctor U).obj (restrP P W.unop)).d 0 1 = 0
  exact (congrArg (fun m => augW U P W.unop ≫ m) (cechD01W_eq U P W.unop)).symm.trans
    (augW_comp_cechD01W U P W.unop)

end Work.DSF1.Sheaf
