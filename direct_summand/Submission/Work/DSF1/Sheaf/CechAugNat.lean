import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafRestr
import Submission.Work.DSF1.Sheaf.CechSheafTerm
import Submission.Work.DSF1.Sheaf.SSEBasic
import Submission.Work.DSF1.Sheaf.SSECore
import Submission.Work.DSF1.Sheaf.CechAug
import Submission.Work.DSF1.Sheaf.FlasqueDevissage

/-!
# The augmentation `restrL P (iSup U) ⟶ Č⁰(U, P)`

For a scheme `X`, a family of opens `U : ι → X.Opens` and a presheaf of abelian groups
`P : X.Opensᵒᵖ ⥤ AddCommGrpCat`, we construct the augmentation

`cechAugNat U P : restrL P (iSup U) ⟶ cechSheafTerm U P 0`

of the sheaf-level Čech complex of the family `U`.  Its component at an open `W` is the
`Pi.lift` of the restrictions `P ((iSup U) ⊓ W) ⟶ P ((cechN U 0).obj y ⊓ W)` along the
inclusions `(cechN U 0).obj y ≤ iSup U` (the opens of the degree zero simplices of the
Čech nerve of `U` are contained in `iSup U`).

The degree zero simplices of the Čech nerve of `U` are indexed by `Fin 1 → ι`, and
`(cechN U 0).obj y = ∏ᶜ (U ∘ y)`, so that `cechAugNat U P` is morally the map
`P ((iSup U) ⊓ W) ⟶ ∏ i, P (U i ⊓ W)` given by the restrictions.

For convenience we also provide the "concrete" form of the ingredients, in which all the
presheaves are evaluated at opens: `secU U P W` is the value `P ((iSup U) ⊓ W)`,
`cech0 U P W` is the value of the degree zero term at `W`, `augW U P W` is the component of
the augmentation at `W` and `cechRestrW U P h` is the restriction map of the degree zero
term, so that the naturality of the augmentation becomes the identity
`augW_naturality` between these concrete morphisms.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The component of a `Pi.lift` at an element, in a concrete category. -/
lemma pi_lift_apply {ι' : Type u} {A : AddCommGrpCat.{u}} (G : ι' → AddCommGrpCat.{u})
    (g : (i : ι') → A ⟶ G i) (i : ι') (z : ↥A) :
    (Pi.π G i) ((Pi.lift g) z) = (g i) z := by
  rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]

/-! ## The concrete form of the augmentation and of the Čech restriction maps -/

/-- The sections of `P` over `(iSup U) ⊓ W`, i.e. the value of `restrL P (iSup U)` at `W`. -/
abbrev secU {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) : AddCommGrpCat.{u} :=
  P.obj (op (iSup U ⊓ W))

/-- The degree zero term of the sheaf-level Čech complex, evaluated at `W`. -/
noncomputable abbrev cech0 {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) : AddCommGrpCat.{u} :=
  ∏ᶜ (fun y : (cechN U 0).I => P.obj (op ((cechN U 0).obj y ⊓ W)))

/-- The `y`-th component of the augmentation: the restriction of a section over `(iSup U) ⊓ W`
to the open `(cechN U 0).obj y ⊓ W`. -/
noncomputable def augComp {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (y : (cechN U 0).I) :
    secU U P W ⟶ P.obj (op ((cechN U 0).obj y ⊓ W)) :=
  P.map (homOfLE (inf_le_inf (cechN_obj_le_iSup U 0 y) le_rfl)).op

@[simp]
lemma augComp_apply {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (y : (cechN U 0).I) (z : ↥(secU U P W)) :
    augComp U P W y z = P.map (homOfLE (inf_le_inf (cechN_obj_le_iSup U 0 y) le_rfl)).op z := rfl

@[simp]
lemma augComp_eq {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (y : (cechN U 0).I) :
    augComp U P W y
      = P.map (homOfLE (inf_le_inf (cechN_obj_le_iSup U 0 y) le_rfl)).op := rfl

/-- The component at `W` of the augmentation of the sheaf-level Čech complex. -/
noncomputable def augW {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) : secU U P W ⟶ cech0 U P W :=
  Pi.lift (fun y : (cechN U 0).I => augComp U P W y)

lemma augW_π {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (y : (cechN U 0).I) :
    augW U P W ≫ Pi.π (fun y' : (cechN U 0).I => P.obj (op ((cechN U 0).obj y' ⊓ W))) y
      = augComp U P W y :=
  Pi.lift_comp_π _ _

lemma augW_apply_π {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : X.Opens) (y : (cechN U 0).I) (z : ↥(secU U P W)) :
    (Pi.π (fun y' : (cechN U 0).I => P.obj (op ((cechN U 0).obj y' ⊓ W))) y) (augW U P W z)
      = augComp U P W y z :=
  pi_lift_apply _ _ _ _

/-- The restriction map of the degree zero Čech term, in concrete form. -/
noncomputable def cechRestrW {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {W W' : X.Opens} (h : W' ≤ W) : cech0 U P W ⟶ cech0 U P W' :=
  Pi.lift (fun y : (cechN U 0).I =>
    Pi.π (fun y' : (cechN U 0).I => P.obj (op ((cechN U 0).obj y' ⊓ W))) y ≫
      P.map (homOfLE (inf_le_inf_left ((cechN U 0).obj y) h)).op)

lemma cechRestrW_π {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {W W' : X.Opens} (h : W' ≤ W) (y : (cechN U 0).I) :
    cechRestrW U P h ≫ Pi.π (fun y' : (cechN U 0).I => P.obj (op ((cechN U 0).obj y' ⊓ W'))) y
      = Pi.π (fun y' : (cechN U 0).I => P.obj (op ((cechN U 0).obj y' ⊓ W))) y ≫
        P.map (homOfLE (inf_le_inf_left ((cechN U 0).obj y) h)).op :=
  Pi.lift_comp_π _ _

/-- The concrete restriction map of the degree zero Čech term is the restriction map of the
sheaf-level Čech term. -/
lemma cechRestrW_eq_map {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {W W' : X.Opens} (h : W' ≤ W) :
    cechRestrW U P h = (cechSheafTerm U P 0).map (homOfLE h).op := by
  refine Pi.hom_ext _ _ (fun y => ?_)
  rw [cechRestrW_π]
  exact (Work.DSF1.Cech.cechComplexFunctor_map_pi U
    ((restrPFunctor P).map (homOfLE h).op) 0 y).symm

/-- **The naturality of the augmentation, in concrete form.** -/
lemma augW_naturality {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {W W' : X.Opens} (h : W' ≤ W) :
    P.map (homOfLE (inf_le_inf_left (iSup U) h)).op ≫ augW U P W'
      = augW U P W ≫ cechRestrW U P h := by
  refine Pi.hom_ext _ _ (fun y => ?_)
  rw [Category.assoc, Category.assoc, augW_π, augComp_eq, cechRestrW_π, ← Category.assoc,
    augW_π, augComp_eq]
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg (fun m => P.map m) (Subsingleton.elim _ _)

/-! ## The augmentation, in the vocabulary of `restrL` and `cechSheafTerm` -/

/-- The component at `W` of the augmentation of the sheaf-level Čech complex. -/
noncomputable abbrev augApp {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : (X.Opens)ᵒᵖ) : (restrL P (iSup U)).obj W ⟶ (cechSheafTerm U P 0).obj W :=
  augW U P W.unop

lemma augApp_π {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : (X.Opens)ᵒᵖ) (y : (cechN U 0).I) :
    augApp U P W ≫
        Pi.π (fun y' : (cechN U 0).I => (restrP P W.unop).obj (op ((cechN U 0).obj y'))) y
      = augComp U P W.unop y := by
  rw [augApp]
  exact augW_π U P W.unop y

lemma augApp_apply_π {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (W : (X.Opens)ᵒᵖ) (y : (cechN U 0).I) (z : ↥((restrL P (iSup U)).obj W)) :
    (Pi.π (fun y' : (cechN U 0).I => (restrP P W.unop).obj (op ((cechN U 0).obj y'))) y)
        (augApp U P W z)
      = augComp U P W.unop y z := by
  rw [augApp]
  exact augW_apply_π U P W.unop y z

/-- The naturality of the augmentation: it is compatible with the restriction maps. -/
lemma augApp_naturality {ι : Type u} (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {W W' : (X.Opens)ᵒᵖ} (f : W ⟶ W') :
    (restrL P (iSup U)).map f ≫ augApp U P W' = augApp U P W ≫ (cechSheafTerm U P 0).map f := by
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf]
  show P.map (homOfLE (inf_le_inf_left (iSup U) (leOfHom f.unop))).op ≫ augW U P W'.unop
      = augW U P W.unop ≫ cechRestrW U P (leOfHom f.unop)
  exact augW_naturality U P (leOfHom f.unop)

/-- **The augmentation of the sheaf-level Čech complex.**  At an open `W`, it is the family of
restrictions of a section over `(iSup U) ⊓ W` to the opens `(cechN U 0).obj y ⊓ W`. -/
noncomputable def cechAugNat {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    restrL P (iSup U) ⟶ cechSheafTerm U P 0 where
  app W := augApp U P W
  naturality {W W'} f := augApp_naturality U P f

end Work.DSF1.Sheaf
