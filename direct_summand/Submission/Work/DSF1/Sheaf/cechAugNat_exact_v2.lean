import Mathlib
import Submission.Work.DSF1.Sheaf.CechAugNat
import Submission.Work.DSF1.Sheaf.SSECore
import Submission.Work.DSF1.Sheaf.cechAugNat_comp_cechSheafD
import Submission.Work.DSF1.Sheaf.cechAugNat_injective
import Submission.Work.DSF1.Sheaf.isCompatible_cech_sections

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

/-!
# Exactness of the sheaf-level Čech complex in degree zero

`cechAugNat_exact_v2`: for a sheaf `P` of abelian groups on a scheme `X`, a family of opens
`U : ι → X.Opens`, an open `W` with `W ≤ ⨆ U` and a `0`-cochain `x` of the sheaf-level Čech
complex `Č⁰(U, P)` over `W`, the differential of `x` vanishes if and only if `x` is the image
of a section of `P` over `⨆ U ⊓ W` under the augmentation `cechAugNat U P`.

The two directions are:

* `⟸`: the composite `cechAugNat U P ≫ cechSheafD U P 0` is zero
  (`cechAugNat_comp_cechSheafD`), so anything in the image of the augmentation is a cocycle.
* `⟹`: a `0`-cocycle is a compatible family on the cover `{(cechN U 0).obj a ⊓ W}`
  (`isCompatible_cech_sections`), which glues by the sheaf condition
  (`TopCat.Sheaf.existsUnique_gluing'`) to a section over `(⨆ a, (cechN U 0).obj a) ⊓ W = ⨆ U ⊓ W`;
  the components of the augmentation are exactly the restrictions used in the gluing.
-/

/-- The opens of the degree zero Čech nerve of `U`, intersected with a fixed open `W`, still
cover `(⨆ U) ⊓ W`: `(cechN U 0).obj (fun _ => i) = U i` (`cechN_obj_const`). -/
lemma le_iSup_cechN_zero_inf {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (W : X.Opens) :
    iSup U ⊓ W ≤ iSup (fun a : (cechN U 0).I => (cechN U 0).obj a ⊓ W) := by
  rw [iSup_inf_eq]
  refine iSup_le fun i => ?_
  exact (le_of_eq (congrArg (fun Z : X.Opens => Z ⊓ W) (cechN_obj_const U i)).symm).trans
    (le_iSup (fun a : (cechN U 0).I => (cechN U 0).obj a ⊓ W) (fun _ : Fin 1 => i))

/-- The composite of the augmentation with the degree zero Čech differential vanishes
elementwise: the image of the augmentation consists of cocycles. -/
lemma augApp_comp_cechSheafD_apply {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W : (X.Opens)ᵒᵖ)
    (y : (restrL P (iSup U)).obj W) :
    ((cechSheafD U P 0).app W) ((cechAugNat U P).app W y) = 0 := by
  have h := congrArg (fun (m : restrL P (iSup U) ⟶ cechSheafTerm U P (0+1)) =>
      (ConcreteCategory.hom (m.app W)) y) (cechAugNat_comp_cechSheafD U P)
  simpa [NatTrans.comp_app, ConcreteCategory.comp_apply] using h

theorem cechAugNat_exact_v2 {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (hP : TopCat.Presheaf.IsSheaf P) (W : Opposite (X.Opens)) (hW : W.unop ≤ iSup U)
    (x : (cechSheafTerm U P 0).obj W) :
    ((cechSheafD U P 0).app W) x = 0 ↔
      ∃ y : (restrL P (iSup U)).obj W, (cechAugNat U P).app W y = x := by
  constructor
  · -- a `0`-cocycle is a compatible family on the cover `(cechN U 0).obj · ⊓ W`
    intro hx
    have hcover : iSup U ⊓ W.unop ≤
        iSup (fun a : (cechN U 0).I => (cechN U 0).obj a ⊓ W.unop) :=
      le_iSup_cechN_zero_inf U W.unop
    have hcompat : TopCat.Presheaf.IsCompatible (X := X.toTopCat) P
        (fun a : (cechN U 0).I => (cechN U 0).obj a ⊓ W.unop)
        (fun a : (cechN U 0).I =>
          (Pi.π (fun a' : (cechN U 0).I =>
            P.obj (op ((cechN U 0).obj a' ⊓ W.unop))) a) x) :=
      isCompatible_cech_sections U P W.unop x hx
    -- glue the compatible family
    obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := AddCommGrpCat.{u}) ⟨P, hP⟩
      (fun a : (cechN U 0).I => (cechN U 0).obj a ⊓ W.unop) (iSup U ⊓ W.unop)
      (fun a => homOfLE (inf_le_inf (cechN_obj_le_iSup U 0 a) le_rfl)) hcover
      (fun a : (cechN U 0).I =>
        (Pi.π (fun a' : (cechN U 0).I =>
          P.obj (op ((cechN U 0).obj a' ⊓ W.unop))) a) x)
      hcompat
    -- the components of the augmentation are the restrictions used in the gluing
    refine ⟨y, ?_⟩
    refine eq_of_π_eq (fun a : (cechN U 0).I =>
      (restrP P W.unop).obj (op ((cechN U 0).obj a))) _ _ (fun a => ?_)
    change (ConcreteCategory.hom (Pi.π (fun a' : (cechN U 0).I =>
        (restrP P W.unop).obj (op ((cechN U 0).obj a'))) a))
        ((ConcreteCategory.hom (augApp U P W)) y) =
      (ConcreteCategory.hom (Pi.π (fun a' : (cechN U 0).I =>
        (restrP P W.unop).obj (op ((cechN U 0).obj a'))) a)) x
    rw [augApp_apply_π, augComp_apply]
    exact hy a
  · -- the image of the augmentation consists of cocycles
    rintro ⟨y, hy⟩
    rw [← hy]
    exact augApp_comp_cechSheafD_apply U P W y

end Work.DSF1.Sheaf
