import Mathlib
import Submission.Work.DSEQ0.cechShZ_aux

namespace Work.DSEQ0

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits

/-- For an open `U` of a scheme equal to `⊤` and any module `M`: the unit of the restriction
adjunction `restrictFunctor U.ι ⊣ pushforward U.ι`, evaluated at `M`, is an isomorphism. Indeed
its component over `V` is the restriction map of `M` along `U ⊓ V ≤ V`
(`Scheme.Modules.restrictAdjunction_unit_app_app`), and `U = ⊤` makes the source `⊤ ⊓ V = V`. -/
theorem isIso_restrictAdjunction_unit (X : AlgebraicGeometry.Scheme.{u})
    (M : X.Modules) (U : X.Opens) (hU : U = ⊤) :
    IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) := by
  subst hU
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have h : (⊤ : X.Opens).ι ''ᵁ (⊤ : X.Opens).ι ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, top_inf_eq]
  rw [show homOfLE (Scheme.Hom.image_preimage_le (⊤ : X.Opens).ι V) = eqToHom h from
    Subsingleton.elim _ _]
  exact (M.presheaf.mapIso (eqToIso h).op).isIso_hom

theorem isIso_psiUnitHom (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.IsIso (Work.DSEQ0.psiUnitHom X) := by
  haveI h1 : IsIso ((Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app
      (SheafOfModules.unit X.ringCatSheaf)) := isIso_restrictAdjunction_unit X _ ⊤ rfl
  haveI h2 : IsIso ((Scheme.Modules.pushforward (⊤ : X.Opens).ι).map
      (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).hom) :=
    (Functor.mapIso (Scheme.Modules.pushforward (⊤ : X.Opens).ι)
      (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι)).isIso_hom
  rw [show Work.DSEQ0.psiUnitHom X =
      (Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pushforward (⊤ : X.Opens).ι).map
          (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).hom from rfl]
  exact (asIso ((Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app
        (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      Functor.mapIso (Scheme.Modules.pushforward (⊤ : X.Opens).ι)
        (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι)).isIso_hom

end Work.DSEQ0
