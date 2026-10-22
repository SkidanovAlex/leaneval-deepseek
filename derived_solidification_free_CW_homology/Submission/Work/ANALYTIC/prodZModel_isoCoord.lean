import Mathlib
import Submission.Work.ANALYTIC.kTildeDefs
import Submission.Work.ANALYTIC.ProdZModel
import Submission.Work.ANALYTIC.ProdZAux
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ANALYTIC.LcZIsoCz
import Submission.Work.ANALYTIC.prodZModel_isoC

/-!
# `∏_ℕ ℤ` is the product `∏ᶜ (fun _ : ℕ => LCZ)`, *with* its coordinate projections (AN2)

`Work.ANALYTIC.prodZModel` is the light condensed abelian group whose `S`-points are
*definitionally* the families `ℕ → C(S,ℤ)` of continuous `ℤ`-valued functions (a model of `∏_ℕ ℤ`),
while `Work.ANALYTIC.prodLCZ = ∏ᶜ (fun _ : ℕ => LCZ)` is the `ℕ`-indexed product of copies of the
locally-constant-`ℤ` model `LCZ`.

The present file upgrades the object-level identification `prodZModel ≅ ∏ℤ ≅ prodLCZ` of
`Submission/Work/ANALYTIC/prodZModel_isoC.lean` to a *coordinate-wise* one:

* `projModel j : prodZModel ⟶ LCZ` is the `j`-th coordinate of the explicit model,
  `x ↦ (s ↦ x j s)`;
* `isIso_lift_projModel` says that `Pi.lift (fun j => projModel j) : prodZModel ⟶ prodLCZ`
  (the currying bijection) is an isomorphism, so that these coordinates *are* the product
  projections;
* consequently `prodZModel_isoCoord` exhibits an isomorphism `prodZModel ≅ prodLCZ` whose
  composite with the `j`-th projection of `prodLCZ` is, on the *bounded* sequences, exactly
  `coordLCZ j`.  This is the form in which the identification is consumed by the null-sequence
  argument of REFS/03 §3 (AN2 of the blueprint).

The proof of `isIso_lift_projModel` reduces, through the fully faithful `sheafToPresheaf`
(which reflects isomorphisms), to the presheaf-level statement that the currying map
`prodZPresheaf ⟶ ∏ᶜ (fun _ => lcZ)` is an isomorphism.  There the two ingredients are

* `isIso_pi_lift_projLC`: `Pi.lift (fun j => projLC j)` is an isomorphism, because the fan
  `prodCone` of `ProdZAux` is a limit cone and `Fan.isLimit c ↔ IsIso (Pi.lift c.proj)`;
* `Pi.mapIso` applied to the isomorphism `Cz ≅ lcZ` of `LcZIsoCz`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## The coordinate projections of the explicit model `∏_ℕ ℤ` -/

/-- The `j`-th coordinate projection of the explicit model `prodZModel = ∏_ℕ ℤ`, landing in the
locally-constant-`ℤ` model `LCZ`: on `S`-points it sends a family `(x_n)_{n : ℕ}` of continuous
`ℤ`-valued functions on `S` to `x_j`, viewed as a locally constant function. -/
noncomputable def projModel (j : ℕ) : prodZModel ⟶ Work.ATOM.ZS.Unred.LCZ :=
  ObjectProperty.homMk (projLC j ≫ lcZIsoCz.symm.hom)

/-- The defining property of `projModel`: its underlying natural transformation is `projLC j`
followed by the identification `Cz ≅ lcZ` of continuous and locally constant `ℤ`-valued
functions. -/
theorem projModel_hom (j : ℕ) : (projModel j).hom = projLC j ≫ CzTolcZ := by
  rw [projModel, ObjectProperty.homMk_hom]
  rfl

/-- The composite of the inclusion `boundedSeqIncl : ∏^bnd ℤ ⟶ ∏ℤ` with the `j`-th coordinate of
`∏ℤ` is the `j`-th coordinate projection `coordLCZ j` of `∏^bnd ℤ`.  This is the compatibility of
the coordinates with the inclusion of the bounded sequences. -/
theorem boundedSeqIncl_projModel (j : ℕ) : boundedSeqIncl ≫ projModel j = coordLCZ j := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  ext S x
  apply LocallyConstant.ext
  intro s
  rfl

/-! ## The presheaf-level currying isomorphism -/

/-- The `ℕ`-indexed product `∏ᶜ (fun _ : ℕ => Cz)` of copies of the presheaf `Cz` of continuous
`ℤ`-valued functions has `Pi.lift (fun j => projLC j)` as its currying map; since the fan
`prodCone` is a limit cone (`prodCone_isLimit`) and a fan is limiting exactly when its `Pi.lift`
is an isomorphism, this currying map is an isomorphism. -/
theorem isIso_pi_lift_projLC : IsIso (Pi.lift (fun j : ℕ => projLC j)) := by
  have h := (Fan.nonempty_isLimit_iff_isIso_piLift (c := (prodCone : Fan (fun _ : ℕ => Cz)))).mp
    ⟨(prodCone_isLimit : IsLimit (prodCone : Fan (fun _ : ℕ => Cz)))⟩
  rwa [show Fan.proj (prodCone : Fan (fun _ : ℕ => Cz)) = (fun j : ℕ => projLC j) from
    fan_mk_proj prodZPresheaf projLC] at h

/-- The presheaf of all families `ℕ → C(-,ℤ)` is the product of the presheaves `C(-,ℤ)` of
continuous `ℤ`-valued functions, via the currying map composed with the identification
`Cz ≅ lcZ`. -/
noncomputable def phiIso :
    prodZPresheaf ≅ (∏ᶜ (fun _ : ℕ => lcZ) : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ) :=
  haveI := isIso_pi_lift_projLC
  asIso (Pi.lift (fun j : ℕ => projLC j)) ≪≫ Pi.mapIso (fun _ : ℕ => lcZIsoCz.symm)

/-- The `j`-th projection of `phiIso` is the `j`-th coordinate. -/
theorem phiIso_hom_π (j : ℕ) :
    phiIso.hom ≫ Pi.π (fun _ : ℕ => lcZ) j = projLC j ≫ lcZIsoCz.symm.hom := by
  rw [show phiIso.hom = Pi.lift (fun j : ℕ => projLC j) ≫
      (Pi.mapIso (fun _ : ℕ => lcZIsoCz.symm)).hom from rfl]
  rw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc, Pi.lift_comp_π]

/-! ## The underlying presheaf of a small product of sheaves -/

/-- **The underlying presheaf of `∏ᶜ F` is the product of the underlying presheaves**: since
`sheafToPresheaf` creates limits, the presheaf underlying the `ℕ`-indexed product of a family of
light condensed abelian groups is the `ℕ`-indexed product of the underlying presheaves. -/
noncomputable def sheafPiIso (F : ℕ → LightCondAb) :
    (∏ᶜ F).obj ≅ (∏ᶜ (fun j => (F j).obj) : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ) :=
  let Ds : Discrete ℕ ⥤ LightCondAb := Discrete.functor F
  IsLimit.conePointUniqueUpToIso
      (PreservesLimit.preserves (show IsLimit (limit.cone Ds) from limit.isLimit Ds)).some
      (limit.isLimit (Ds ⋙ sheafToPresheaf _ _)) ≪≫
    (Pi.isoLimit (Ds ⋙ sheafToPresheaf _ _)).symm

/-- The `j`-th projection of the product of sheaves agrees, under `sheafPiIso`, with the `j`-th
projection of the product of the underlying presheaves. -/
theorem sheafPiIso_hom_π (F : ℕ → LightCondAb) (j : ℕ) :
    (sheafPiIso F).hom ≫ Pi.π (fun j => (F j).obj) j = (Pi.π F j).hom := by
  let Ds : Discrete ℕ ⥤ LightCondAb := Discrete.functor F
  let shP := sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let X := Ds ⋙ shP
  haveI : HasProduct fun j => X.obj { as := j } := inferInstanceAs (HasProduct fun j => (F j).obj)
  have h2 : (Pi.isoLimit X).inv ≫ Pi.π (fun j => (F j).obj) j = limit.π X (Discrete.mk j) :=
    Pi.isoLimit_inv_π X j
  rw [show (sheafPiIso F).hom = (IsLimit.conePointUniqueUpToIso
      (PreservesLimit.preserves (show IsLimit (limit.cone Ds) from limit.isLimit Ds)).some
      (limit.isLimit X)).hom ≫ (Pi.isoLimit X).inv from rfl]
  rw [Category.assoc, h2]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk j)

/-- The version of `sheafPiIso` for the constant family `LCZ`, with the underlying presheaf of
`LCZ` displayed as `lcZ` (definitionally the same object). -/
noncomputable def sheafPiIsoLCZ : (∏ᶜ (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ)).obj ≅
    (∏ᶜ (fun _ : ℕ => lcZ) : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ) :=
  sheafPiIso (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ)

/-- Projection compatibility of `sheafPiIsoLCZ`. -/
theorem sheafPiIsoLCZ_hom_π (j : ℕ) :
    sheafPiIsoLCZ.hom ≫ Pi.π (fun _ : ℕ => lcZ) j
      = (Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j).hom :=
  sheafPiIso_hom_π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j

/-! ## The currying isomorphism `prodZModel ⟶ prodLCZ` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The currying map `∏_ℕ ℤ ⟶ ∏ᶜ (fun _ : ℕ => LCZ)` is an isomorphism.**  Since
`sheafToPresheaf` is fully faithful, it reflects isomorphisms; and on underlying presheaves the
currying map is `phiIso` (a composite of isomorphisms): the `j`-th projection of
`sheafToPresheaf.map (Pi.lift (fun j => projModel j)) ≫ sheafPiIsoLCZ.hom` is the currying map at
`j`, i.e. `projLC j` followed by `Cz ≅ lcZ`, which is exactly the `j`-th projection of
`phiIso`. -/
theorem isIso_lift_projModel : IsIso (Pi.lift (fun j : ℕ => projModel j)) := by
  let shP := sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  have hmap : shP.map (Pi.lift (fun j : ℕ => projModel j)) = phiIso.hom ≫ sheafPiIsoLCZ.inv := by
    apply (cancel_mono sheafPiIsoLCZ.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, sheafPiIsoLCZ_hom_π j]
    rw [show (Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j).hom
        = shP.map (Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j) from rfl]
    rw [← shP.map_comp, Pi.lift_comp_π]
    rw [show shP.map (projModel j) = (projModel j).hom from rfl, projModel_hom j, phiIso_hom_π j]
    rfl
  haveI : IsIso (shP.map (Pi.lift (fun j : ℕ => projModel j))) := by
    rw [hmap]
    haveI : IsIso phiIso.hom := phiIso.isIso_hom
    haveI : IsIso sheafPiIsoLCZ.inv := sheafPiIsoLCZ.isIso_inv
    infer_instance
  exact Functor.ReflectsIsomorphisms.reflects shP _

/-- **AN2, coordinate form.**  There is an isomorphism `∏_ℕ ℤ ≅ ∏ᶜ (fun _ : ℕ => LCZ)` whose
`j`-th projection, restricted along the inclusion `∏^bnd ℤ ⊆ ∏ℤ` of the uniformly bounded
sequences, is the `j`-th coordinate projection `coordLCZ j`. -/
theorem prodZModel_isoCoord : ∃ e : CategoryTheory.Iso Work.ANALYTIC.prodZModel Work.ANALYTIC.prodLCZ, ∀ j : ℕ, CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp Work.ANALYTIC.boundedSeqIncl e.hom) (CategoryTheory.Limits.Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j) = Work.ANALYTIC.coordLCZ j := by
  haveI := isIso_lift_projModel
  refine ⟨asIso (Pi.lift (fun j : ℕ => projModel j)), fun j => ?_⟩
  rw [Category.assoc, asIso_hom, Pi.lift_comp_π]
  exact boundedSeqIncl_projModel j

end Work.ANALYTIC
