import Mathlib
import Submission.Work.DSEQ0.AugBasic
import Submission.Work.DSF1.Modules.pushforward_unit_sections

/-!
# Definitions for the augmentation quasi-isomorphism (`Work.DSEQ0.quasiIso_augZ`)

This module contains the vocabulary shared by the proof of the theorem
`Work.DSEQ0.quasiIso_augZ` (the augmented Čech complex of the structure sheaf of `X` along a
finite covering family `U` is a resolution of the structure sheaf) and by the delegated lemmas
supporting it.

* `Work.DSEQ0.sectionsV X V` is the functor "sections over `V`", `X.Modules ⥤ AddCommGrpCat`,
  `M ↦ Γ(M, V)`;
* `Work.DSEQ0.structAb X` is the structure sheaf of `X` as a presheaf of abelian groups (a
  sheaf);
* `Work.DSEQ0.sectionsV_secSheaf` identifies `Γ(V, (j_W)_* 𝒪_W)` with `𝒪_X(W ⊓ V)`.
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-! ## The sections functor -/

/-- Sections of a sheaf of `𝒪_X`-modules over an open `V`, as a functor to abelian groups. -/
noncomputable def sectionsV (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  AlgebraicGeometry.Scheme.Modules.toPresheaf X ⋙
    (CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)

set_option backward.isDefEq.respectTransparency false in
instance sectionsV_additive (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) :
    (sectionsV X V).Additive where
  map_add := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sections functor applied to `M` is `M.presheaf.obj (op V)`. -/
lemma sectionsV_obj (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) (M : X.Modules) :
    (sectionsV X V).obj M = M.presheaf.obj (Opposite.op V) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sections functor maps a morphism to its component at `V`. -/
lemma sectionsV_map (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) {M N : X.Modules}
    (f : M ⟶ N) :
    (sectionsV X V).map f = Scheme.Modules.Hom.app f V := rfl

/-- The sections functor preserves the products occurring in the Čech construction (products in
`X.Modules` are computed pointwise, as are products of presheaves). -/
theorem sectionsV_preservesProduct (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens)
    {I : Type u} (g : I → X.Modules) :
    PreservesLimit (Discrete.functor g) (sectionsV X V) := by
  haveI : PreservesLimitsOfShape (Discrete I)
      ((CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)) :=
    CategoryTheory.Limits.evaluation_preservesLimitsOfShape _
  exact (Limits.comp_preservesLimitsOfShape (AlgebraicGeometry.Scheme.Modules.toPresheaf X)
    ((CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opposite.op V))).preservesLimit

/-! ## The structure sheaf as a presheaf of abelian groups -/

/-- The structure sheaf of `X` as a presheaf of abelian groups.  It is a sheaf. -/
noncomputable abbrev structAb (X : AlgebraicGeometry.Scheme.{u}) :
    (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)).obj

set_option backward.isDefEq.respectTransparency false in
lemma structAb_obj (X : AlgebraicGeometry.Scheme.{u}) (W : X.Opens) :
    (structAb X).obj (Opposite.op W) = AddCommGrpCat.of (X.presheaf.obj (Opposite.op W)) := rfl

lemma structAb_isSheaf (X : AlgebraicGeometry.Scheme.{u}) :
    TopCat.Presheaf.IsSheaf (structAb X) :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj
    (SheafOfModules.unit X.ringCatSheaf)).property

/-- Sections of `(j_W)_* 𝒪_W` over `V` are sections of `𝒪_X` over `W ⊓ V`. -/
theorem sectionsV_secSheaf (X : AlgebraicGeometry.Scheme.{u}) (V W : X.Opens) :
    (sectionsV X V).obj (Work.DSF1.secSheaf W) =
      (structAb X).obj (Opposite.op (W ⊓ V)) :=
  Work.DSF1.Modules.pushforward_unit_sections X W V

/-- The same identification, as an isomorphism. -/
noncomputable def secIso (X : AlgebraicGeometry.Scheme.{u}) (V W : X.Opens) :
    (sectionsV X V).obj (Work.DSF1.secSheaf W) ≅ (structAb X).obj (Opposite.op (W ⊓ V)) :=
  eqToIso (sectionsV_secSheaf X V W)

set_option backward.isDefEq.respectTransparency false in
/-- The identification of `secSheaf`-sections with sections of the structure sheaf, at the level
of the carrier types. -/
lemma sectionsV_secSheaf_coe (X : AlgebraicGeometry.Scheme.{u}) (V W : X.Opens) :
    ((sectionsV X V).obj (Work.DSF1.secSheaf W) : Type u) =
      ((structAb X).obj (Opposite.op (W ⊓ V)) : Type u) :=
  congrArg (fun Y : AddCommGrpCat.{u} => (Y : Type u)) (sectionsV_secSheaf X V W)

/-! ## The coaugmentation for coefficients in abelian groups -/

/-- The coaugmentation `Q(⊤) ⟶ Č⁰` of the Čech complex of a family of opens with coefficients
in a presheaf of abelian groups.  (This is `Work.DSF1.Cech.coaug` with the target category
`AddCommGrpCat` rather than `ModuleCat R`.) -/
noncomputable def coaugAb (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Q.obj (Opposite.op ⊤) ⟶ ((CategoryTheory.cechComplexFunctor U).obj Q).X 0 :=
  Pi.lift (fun x => Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op)

end Work.DSEQ0
