import Mathlib
import Submission.Work.DSF1.Canonical

/-!
# `canonical ⊤` is an isomorphism

`Work.DSF1.canonical V` is the restriction map of the structure sheaf,
`𝒪_X ⟶ (V.ι)_* 𝒪_V`; for `V = ⊤` it is an isomorphism.

Both factors in the definition of `canonical ⊤` are isomorphisms:

* the unit of the adjunction `restrictFunctor ⊤.ι ⊣ pushforward ⊤.ι`.  The open immersion
  `⊤.ι : ↑⊤ ⟶ X` is an isomorphism of schemes (`Scheme.topIso`, with inverse `X.topIso.inv`),
  so `pushforward ⊤.ι` is an equivalence of categories; the unit of an adjunction whose right
  adjoint is an equivalence is invertible;
* the pushforward of the isomorphism `restrictUnitIso ⊤.ι : restrict 𝒪_X ⊤.ι ≅ 𝒪_⊤`.
-/

namespace Work.DSF1.Canonical

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option linter.style.haveILetI false in
theorem isIso_canonical_top {X : AlgebraicGeometry.Scheme.{u}} :
    CategoryTheory.IsIso (Work.DSF1.canonical (⊤ : X.Opens)) := by
  unfold Work.DSF1.canonical
  -- `pushforward ⊤.ι` is an equivalence of categories, since `⊤.ι` is itself an isomorphism of
  -- schemes (`Scheme.topIso`) and `pushforward` sends composition (and identities) to composition.
  haveI hE : Functor.IsEquivalence (Scheme.Modules.pushforward ((⊤ : X.Opens).ι)) :=
    Functor.IsEquivalence.mk' (Scheme.Modules.pushforward X.topIso.inv)
      ((Scheme.Modules.pushforwardComp ((⊤ : X.Opens).ι) X.topIso.inv) ≪≫
        (Scheme.Modules.pushforwardCongr (Scheme.ι_toIso_inv X)) ≪≫
        (Scheme.Modules.pushforwardId _)).symm
      ((Scheme.Modules.pushforwardComp X.topIso.inv ((⊤ : X.Opens).ι)) ≪≫
        (Scheme.Modules.pushforwardCongr (Scheme.toIso_inv_ι X)) ≪≫
        (Scheme.Modules.pushforwardId _))
  let a := (Scheme.Modules.restrictAdjunction ((⊤ : X.Opens).ι)).unit.app
      (SheafOfModules.unit X.ringCatSheaf)
  let b := (Scheme.Modules.pushforward ((⊤ : X.Opens).ι)).map
      (Scheme.Modules.restrictUnitIso ((⊤ : X.Opens).ι)).hom
  -- the unit of the adjunction, at `SheafOfModules.unit X.ringCatSheaf`
  haveI h1 : IsIso a := NatIso.isIso_app_of_isIso _ _
  haveI h0 : IsIso (Scheme.Modules.restrictUnitIso ((⊤ : X.Opens).ι)).hom := Iso.isIso_hom _
  -- the pushforward of the isomorphism `restrict 𝒪_X ⊤.ι ≅ 𝒪_⊤`
  haveI h2 : IsIso b := Functor.map_isIso _ _
  show IsIso (a ≫ b)
  infer_instance

end Work.DSF1.Canonical
