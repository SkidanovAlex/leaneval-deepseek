import Mathlib
import Submission.Work.DSEQ0.cechShZ_aux

/-!
# `Work.DSEQ0.linA_psiUnitHom_psi_proof`

The degree-`0` compatibility of `linA` with the canonical comparison `psiUnitHom`, i.e.
`linA ≫ Γ.map (psiUnitHom X) ≫ (psi ⊤).hom = unitTop`.  This is statement `C1'` of the assembly
of `Work.DSEQ0.cechShZ_compat`.

The proof is an element chase: `linA` sends `a` to `phi a`, `Γ.map (psiUnitHom X)` is (on
`⊤`-sections) the restriction `𝒪_X(⊤) ⟶ 𝒪_X(⊤.ι ''ᵁ (⊤.ι ⁻¹ᵁ ⊤))` (`key2`), and `(psi ⊤).hom`
is the restriction `𝒪_X(⊤.ι ''ᵁ (⊤.ι ⁻¹ᵁ ⊤)) ⟶ 𝒪_X(⊤)`; the two restrictions cancel and the
result is `phiU ⊤ a = unitTop a` (`Work.DSF1.Sheaf.psiFun_apply_phi`).
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSEQ0

universe u

variable (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
  (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))

/-- The `⊤`-component of `Scheme.Modules.restrictUnitIso (⊤.ι)` is the identity. -/
lemma restrictUnitIso_app_apply
    (y : Γ(Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) (⊤ : X.Opens).ι,
      (⊤ : X.Opens).ι ⁻¹ᵁ ⊤)) :
    (Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).hom
      ((⊤ : X.Opens).ι ⁻¹ᵁ ⊤)).hom y = y := by
  simp only [Scheme.Modules.Hom.app, Scheme.Modules.restrictUnitIso,
    Functor.FullyFaithful.preimageIso_hom, SheafOfModules.fullyFaithfulForget,
    PresheafOfModules.isoMk_hom_app, ModuleCat.isoMk_hom,
    Functor.mapIso_hom, Scheme.Opens.ι_appIso, Iso.refl_hom, AddCommGrpCat.hom_id]
  rfl

/-- `Γ.map (psiUnitHom X)` is, on `⊤`-sections, the restriction of the structure sheaf. -/
lemma gammaMap_psiUnitHom_app (x : Γ(X, ⊤)) :
    ((DSMap.GammaA A X f).map (psiUnitHom X)).hom x =
      (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens).ι ''ᵁ
        ((⊤ : X.Opens).ι ⁻¹ᵁ ⊤) ≤ ⊤)).op).hom x := by
  rw [show ((DSMap.GammaA A X f).map (psiUnitHom X)).hom x =
      (Scheme.Modules.Hom.app (psiUnitHom X) ⊤).hom x from rfl]
  rw [psiUnitHom, Scheme.Modules.Hom.comp_app]
  rw [AddCommGrpCat.comp_apply]
  rw [Scheme.Modules.pushforward_map_app]
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  erw [restrictUnitIso_app_apply X]
  rfl

/-- **The compatibility of `linA` with the comparison `psiUnitHom`.** -/
theorem linA_psiUnitHom_psi_proof :
    CategoryTheory.CategoryStruct.comp (linA A X f)
        (CategoryTheory.CategoryStruct.comp ((DSMap.GammaA A X f).map (psiUnitHom X))
          (Work.DSF1.Sheaf.psi A X f (⊤ : X.Opens)).hom) =
      DSMap.unitTop A X f := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun a => ?_
  show (Work.DSF1.Sheaf.psi A X f (⊤ : X.Opens)).hom.hom
      (((DSMap.GammaA A X f).map (psiUnitHom X)).hom ((linA A X f).hom a)) =
    (DSMap.unitTop A X f).hom a
  rw [show (linA A X f).hom a = DSMap.phi A X f a from rfl]
  rw [gammaMap_psiUnitHom_app A X f (DSMap.phi A X f a)]
  rw [show (Work.DSF1.Sheaf.psi A X f (⊤ : X.Opens)).hom.hom
      ((X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens).ι ''ᵁ
        ((⊤ : X.Opens).ι ⁻¹ᵁ ⊤) ≤ ⊤)).op).hom (DSMap.phi A X f a)) =
      (X.presheaf.map (eqToHom (Work.DSF1.Sheaf.opens_self (⊤ : X.Opens))).op).hom
        ((X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens).ι ''ᵁ
          ((⊤ : X.Opens).ι ⁻¹ᵁ ⊤) ≤ ⊤)).op).hom (DSMap.phi A X f a))
      from Work.DSF1.Sheaf.psi_hom_apply A X f ⊤ _]
  rw [Work.DSF1.Sheaf.psiFun_apply_phi A X f ⊤ a]
  rfl

end Work.DSEQ0
