import Mathlib
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ANALYTIC.SolidDual
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.ihom_coprod_iso
import Submission.Work.TOOLKIT.Instances
import Submission.Work.ANALYTIC.disc_finsupp_iso_coprod
import Submission.Work.ANALYTIC.pi_option_iso_biprod

/-!
# `ℤ■[T] ≅ ℤ ⊞ ∏_ℕ ℤ` (REFS/03 §4)

For an infinite light profinite set `T` whose discrete dual `C(T,ℤ) = LC T` is a free `ℤ`-module
on the index set `Haar.JIdx = ℕ ∪ {∞}` (`e`, e.g. the Haar/Schauder basis iso `haar_basisIso`),
the solid dual

`ℤ■[T] = solidDual T = ihom (C(T,ℤ)_disc) ℤ`

splits as the biproduct of `ℤ` (the "constant function" coordinate) and `∏_ℕ ℤ`
(`Work.ANALYTIC.prodZ`, the coordinates of the enumerated new points).

The route is the one of `Submission/Work/ANALYTIC/MuT_Route.lean`, step 3:

1. `e` transports along the discrete functor: `Cdisc T ≅ disc (ℤ[JIdx])`
   (`Cdiscrete_iso`), and `disc (ℤ[JIdx]) ≅ ∐_j Z` since `ℤ[JIdx]` is the coproduct of `JIdx`
   copies of `ℤ` and `disc` is a left adjoint (`disc_finsupp_iso_coprod`);
2. `ihom` is contravariant in the first variable, so `solidDual T ≅ (ihom (∐_j Z)).obj Z`;
3. `ihom` turns coproducts in the first variable into products of internal homs
   (`ihom_coprod_iso`), and `Z ⟹ Z ≅ Z` (`MonoidalClosed.unitIsoSelf`), so
   `(ihom (∐_j Z)).obj Z ≅ ∏_j Z`;
4. finally `∏_{ℕ∪{∞}} Z ≅ Z ⊞ ∏_ℕ Z`, i.e. the product over `ℕ ∪ {∞}` splits as the product over
   the one-point set `{∞}` (which is `Z`) and the product over `ℕ` (which is `prodZ`),
   using that a biproduct is a product (`pi_option_iso_biprod`).
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint

open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-- The internal hom of the unit into itself is the unit. -/
def ihom_Z_Z_iso : (CategoryTheory.ihom Z).obj Z ≅ Z :=
  MonoidalClosed.unitIsoSelf Z

/-- **Internal hom out of a coproduct of copies of `Z`.**  The internal hom of the coproduct
`∐_j Z` into `Z` is the product of the (trivial) internal homs `Z ⟹ Z ≅ Z`, i.e. `∏_j Z`.

This is `ihom_coprod_iso` (`[∐_j A_j, Z] ≅ ∏_j [A_j, Z]`) combined with `Z ⟹ Z ≅ Z`. -/
theorem ihom_coprod_iso_Z (J : Type) :
    Nonempty (CategoryTheory.Iso ((CategoryTheory.ihom (∐ (fun _ : J => Z))).obj Z)
      (∏ᶜ (fun _ : J => Z))) := by
  obtain ⟨h⟩ := ihom_coprod_iso J (fun _ : J => Z) Z
  exact ⟨h ≪≫ Pi.mapIso (fun _ : J => ihom_Z_Z_iso)⟩

theorem solidDual_iso_biprod (T : LightProfinite.{0}) [Infinite T]
    (e : CategoryTheory.Iso (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T))
      (ModuleCat.of ℤ (Work.ANALYTIC.Haar.JIdx →₀ ℤ))) :
    Nonempty (CategoryTheory.Iso (Work.ANALYTIC.solidDual T)
      (CategoryTheory.Limits.biprod Work.ANALYTIC.Z Work.ANALYTIC.prodZ)) := by
  -- `C(T,ℤ)_disc ≅ ∐_j Z`
  obtain ⟨hdisc⟩ := disc_finsupp_iso_coprod Haar.JIdx
  -- `∏_{ℕ∪{∞}} Z ≅ Z ⊞ ∏_ℕ Z`
  obtain ⟨hpi⟩ := pi_option_iso_biprod
  -- `(ihom (∐_j Z)).obj Z ≅ ∏_j Z`
  obtain ⟨h3⟩ := ihom_coprod_iso_Z Haar.JIdx
  refine ⟨?_⟩
  -- `(ihom X).obj Z` as a functor of `X ∈ LightCondAbᵒᵖ`
  let G : LightCondAbᵒᵖ ⥤ LightCondAb := MonoidalClosed.internalHom.flip.obj Z
  -- transport the module iso `e` along the discrete functor
  have hA : Cdisc T ≅ (LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ (Haar.JIdx →₀ ℤ)) :=
    (Cdiscrete_iso (ModuleCat.of ℤ (Haar.LC T))).some ≪≫
      (LightCondensed.discrete (ModuleCat ℤ)).mapIso e
  -- contravariance of `ihom` in the first variable:
  -- `solidDual T = (ihom (Cdisc T)).obj Z ≅ (ihom (∐_j Z)).obj Z`
  have hcontra : solidDual T ≅ (CategoryTheory.ihom (∐ (fun _ : Haar.JIdx => Z))).obj Z :=
    ((G.mapIso hdisc.op) ≪≫ (G.mapIso hA.op)).symm
  exact hcontra ≪≫ h3 ≪≫ hpi

end

end Work.ANALYTIC
