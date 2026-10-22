import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.ProdZ
import Submission.Work.ANALYTIC.ProdZModel

/-!
# Auxiliary presheaves for the identification `∏ℤ_model ≅ ∏ℤ` (AN2 side condition)

The product `Work.ANALYTIC.prodZ = ∏ᶜ (fun _ : ℕ => Z)` of copies of the constant sheaf `ℤ` is
abstract; the object `Work.ANALYTIC.prodZModel` of `Submission/Work/ANALYTIC/ProdZModel.lean`,
whose `S`-points are *definitionally* the families `ℕ → C(S,ℤ)`, is the concrete model of the same
object.  This file sets up the presheaves used to compare them:

* `Cz` is the presheaf `S ↦ C(S,ℤ)` of continuous `ℤ`-valued functions (equivalently, by
  `LightCondMod.LocallyConstant.functorIsoDiscrete`, the presheaf underlying `Z`);
* `lcZ` is Mathlib's presheaf of locally constant `ℤ`-valued functions (the `Z`-model used by
  `LightCondMod.LocallyConstant`);
* `projLC n` and `prodCone` exhibit `prodZPresheaf` (the presheaf underlying `prodZModel`) as the
  `ℕ`-indexed product of copies of `Cz`.

The two remaining comparisons (`Z.obj ≅ lcZ` and `lcZ ≅ Cz`) are the content of
`Submission/Work/ANALYTIC/ZobjIsoLcZ.lean` and `Submission/Work/ANALYTIC/LcZIsoCz.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The presheaf `S ↦ C(S,ℤ)` of continuous `ℤ`-valued functions; for a light profinite space `S`
these are exactly the locally constant functions, so this is a model of the constant sheaf `ℤ`. -/
noncomputable def Cz : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj d := ModuleCat.of ℤ C(d.unop, ℤ)
  map g := ModuleCat.ofHom
    { toFun := fun x => x.comp (LightProfinite.toTopCat.map g.unop).hom
      map_add' := fun a b => by ext s; rfl
      map_smul' := fun a b => by ext s; rfl }
  map_id := by intro d; ext x; rfl
  map_comp := by intro a b c f g; ext x; rfl

/-- Mathlib's model of the presheaf underlying the constant sheaf `ℤ`: the presheaf of locally
constant `ℤ`-valued functions. -/
noncomputable abbrev lcZ : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ :=
  (LightCondMod.LocallyConstant.functorToPresheaves ℤ).obj (ModuleCat.of ℤ ℤ)

/-- **The presheaf underlying `Z` is Mathlib's locally constant model.** -/
noncomputable def ZobjIsoLcZ : (Z).obj ≅ lcZ :=
  ((sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).mapIso
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ))).symm

/-- The `n`-th coordinate projection `(∏_ℕ C(S,ℤ)) ⟶ C(S,ℤ)`, as a map of presheaves. -/
noncomputable def projLC (n : ℕ) : prodZPresheaf ⟶ Cz where
  app d := ModuleCat.ofHom (LinearMap.proj n : (∀ _ : ℕ, ↥(Cz.obj d)) →ₗ[ℤ] ↥(Cz.obj d))
  naturality d d' f := by ext x; rfl

/-- `prodZPresheaf` as a cone over the constant diagram at `Cz`: the `ℕ`-indexed product of copies
of `Cz`. -/
noncomputable def prodCone : Cone (Discrete.functor (fun _ : ℕ => Cz)) :=
  Fan.mk prodZPresheaf projLC

/-- **The cone `prodCone` is limiting.**  Since limits in a functor category are computed
pointwise, it suffices to check that at every `d` the evaluation of `prodCone` is the concrete
product cone `ModuleCat.productCone` (whose point is, definitionally,
`∏_ℕ ↥(Cz.obj d) = (ℕ → C(d.unop,ℤ))`, the `d`-points of `prodZPresheaf`). -/
noncomputable def prodCone_isLimit : IsLimit prodCone :=
  evaluationJointlyReflectsLimits prodCone fun d =>
    ModuleCat.productConeIsLimit (fun _ : ℕ => Cz.obj d)

/-- **`∏ᶜ (fun _ : ℕ => Cz)` is the presheaf underlying `prodZModel`.** -/
theorem piCz_iso_prodZPresheaf :
    Nonempty ((∏ᶜ (fun _ : ℕ => Cz) : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ) ≅ prodZPresheaf) :=
  ⟨(limit.isLimit (Discrete.functor fun _ : ℕ => Cz)).conePointUniqueUpToIso prodCone_isLimit⟩

/-- **The presheaf underlying `∏ᶜ (fun _ : ℕ => Z)` is the `ℕ`-indexed product of copies of the
presheaf underlying `Z`.**  This is because `sheafToPresheaf` creates limits
(`CategoryTheory.Sheaf.createsLimitsOfShape`). -/
theorem prodZObj_iso_piZobj :
    Nonempty ((prodZ).obj ≅ (∏ᶜ (fun _ : ℕ => (Z).obj) : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ)) :=
  let Ds : Discrete ℕ ⥤ LightCondAb := Discrete.functor (fun _ : ℕ => Z)
  ⟨IsLimit.conePointUniqueUpToIso
      (PreservesLimit.preserves (show IsLimit (limit.cone Ds) from limit.isLimit Ds)).some
      (limit.isLimit (Ds ⋙ sheafToPresheaf _ _)) ≪≫
    (Pi.isoLimit (Ds ⋙ sheafToPresheaf _ _)).symm⟩

end Work.ANALYTIC
