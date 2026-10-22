import Mathlib
import Submission.Work.ANALYTIC.SolidDual
import Submission.Work.ANALYTIC.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.ANALYTIC.ihom_coprod_iso
import Submission.Work.ANALYTIC.disc_finsupp_iso_coprod
import Submission.Work.ANALYTIC.finite_iso_sigma_pt
import Submission.Work.ATOM.projective_P

/-!
# `ℤ[T] ≅ ℤ■[T]` for finite light profinite `T`

For a *finite* light profinite set `T` the solid dual `ℤ■[T] = ihom (C(T,ℤ)_disc) ℤ` is the free
light condensed abelian group `ℤ[T]` on `T`.

Both sides are the free light condensed abelian group of rank `|T|`, i.e. the coproduct of `|T|`
copies of the monoidal unit `ℤ`:

* `ℤ[T] ≅ ∐_{t : T} ℤ` because `ℤ[-]` is a left adjoint and `T = ∐_{t : T} ⋆`
  (`finite_iso_sigma_pt`), while `ℤ[⋆] ≅ ℤ` (`Work.ATOM.unitIso`);
* `C(T,ℤ)_disc = Cdisc T ≅ ∐_{t : T} ℤ`: `Cdisc T = functor (LocallyConstant T ℤ)` is the discrete
  light condensed abelian group on the free `ℤ`-module `↥T →₀ ℤ` of rank `|T|`, and the discrete
  functor is a left adjoint, hence preserves coproducts (`disc_finsupp_iso_coprod`);
* `ihom` is contravariant in its first variable and turns coproducts into products
  (`ihom_coprod_iso`), `ℤ ⟹ ℤ ≅ ℤ` (`MonoidalClosed.unitIsoSelf`), and for a finite index the
  product is the coproduct (`biproductIso`).
-/

namespace Work.ANALYTIC

-- `haveI` is used below for a `Prop`-valued typeclass (`HasFiniteBiproducts`); the instance must
-- stay an instance for `biproductIso` to be applicable.
set_option linter.style.haveILetI false

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-! ## The free object `ℤ[T]` -/

/-- The composite functor `ℤ[-]` from light profinite sets to light condensed abelian groups. -/
abbrev zfreeFunctor : LightProfinite.{0} ⥤ LightCondAb :=
  lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ

/-- `ℤ[⋆] ≅ ℤ = 𝟙_ LightCondAb`: the free light condensed abelian group on a point is the
monoidal unit. -/
def zfreePtIso : zfreeFunctor.obj (LightProfinite.of PUnit.{1}) ≅ Z :=
  Work.ATOM.unitIso.symm

/-- **`ℤ[T]` is the coproduct of `|T|` copies of the unit.**  Transporting the coproduct
decomposition `T = ∐_{t : T} ⋆` of a finite light profinite set along the left adjoint `ℤ[-]`. -/
noncomputable def zfreeIsoSigma (T : LightProfinite.{0}) [Finite T]
    (e : T ≅ CategoryTheory.Limits.sigmaObj (fun _ : ↥T => LightProfinite.of PUnit.{1})) :
    (LightCondensed.free (R := ℤ)).obj T.toCondensed ≅
      CategoryTheory.Limits.sigmaObj (fun _ : ↥T => Z) :=
  zfreeFunctor.mapIso e ≪≫
    PreservesCoproduct.iso zfreeFunctor (fun _ : ↥T => LightProfinite.of PUnit.{1}) ≪≫
    Sigma.mapIso (fun _ : ↥T => zfreePtIso)

/-! ## `C(T,ℤ)_disc` for finite `T` -/

/-- For a finite light profinite set the locally constant `ℤ`-valued functions are the functions
(the space is discrete), as a `ℤ`-linear equivalence. -/
noncomputable def locallyConstantFunLinearEquiv (T : LightProfinite.{0}) [Finite T] :
    LocallyConstant ↥T ℤ ≃ₗ[ℤ] (↥T → ℤ) where
  toFun f := fun t => f t
  map_add' f g := by ext t; rfl
  map_smul' c f := by ext t; rfl
  invFun g := ⟨g, (IsLocallyConstant.iff_continuous g).mpr continuous_of_discreteTopology⟩
  left_inv f := by ext t; rfl
  right_inv g := by ext t; rfl

/-- `LocallyConstant ↥T ℤ ≅ ↥T →₀ ℤ` for a finite light profinite set `T`: the "indicator basis"
identification `λ ↦ Σ_t λ(t) · δ_t` of the free `ℤ`-module of rank `|T|`. -/
noncomputable def locallyConstantIsoFinsupp (T : LightProfinite.{0}) [Finite T] :
    ModuleCat.of ℤ (LocallyConstant ↥T ℤ) ≅ ModuleCat.of ℤ (↥T →₀ ℤ) :=
  (locallyConstantFunLinearEquiv T).toModuleIso ≪≫
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ↥T).toModuleIso.symm

/-- **`C(T,ℤ)_disc` is the coproduct of `|T|` copies of `ℤ`** for a finite light profinite set
`T`. -/
theorem CdiscIsoSigmaUnit (T : LightProfinite.{0}) [Finite T] :
    Nonempty (Cdisc T ≅ CategoryTheory.Limits.sigmaObj (fun _ : ↥T => Z)) := by
  obtain ⟨h1⟩ := Cdiscrete_iso (ModuleCat.of ℤ (LocallyConstant ↥T ℤ))
  obtain ⟨hd⟩ := disc_finsupp_iso_coprod ↥T
  exact ⟨h1 ≪≫ (LightCondensed.discrete (ModuleCat ℤ)).mapIso (locallyConstantIsoFinsupp T) ≪≫ hd⟩

/-! ## The internal hom of a finite coproduct of copies of the unit -/

/-- The internal hom of the unit into the unit is the unit. -/
def ihomZZIso : (CategoryTheory.ihom Z).obj Z ≅ Z :=
  MonoidalClosed.unitIsoSelf Z

/-- **Contravariance of `ihom (-) ℤ`.**  An isomorphism `A ≅ B` induces an isomorphism
`(ihom B).obj ℤ ≅ (ihom A).obj ℤ`. -/
noncomputable def ihomPreIso {A B : LightCondAb} (e : A ≅ B) :
    (CategoryTheory.ihom B).obj Z ≅ (CategoryTheory.ihom A).obj Z :=
  (MonoidalClosed.internalHom.flip.obj Z).mapIso e.op

/-- **Internal hom out of a finite coproduct of copies of the unit.**  For a finite index type,
`[∐_j ℤ, ℤ] ≅ ∐_j ℤ`: `ihom_coprod_iso` computes the left hand side as the product `∏_j (ℤ ⟹ ℤ)`,
each factor is `ℤ` (`unitIsoSelf`), and a finite product in `LightCondAb` is a coproduct. -/
theorem ihomCoprodZ (J : Type) [Finite J] :
    Nonempty (CategoryTheory.Iso ((CategoryTheory.ihom (∐ (fun _ : J => Z))).obj Z)
      (∐ (fun _ : J => Z))) := by
  haveI : HasFiniteBiproducts LightCondAb := HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨h⟩ := ihom_coprod_iso J (fun _ : J => Z) Z
  exact ⟨h ≪≫ Pi.mapIso (fun _ : J => ihomZZIso) ≪≫ biproductIso (fun _ : J => Z)⟩

/-! ## The main theorem -/

theorem solidDual_iso_zfree_of_finite (T : LightProfinite.{0}) [Finite T] :
    Nonempty ((LightCondensed.free (R := ℤ)).obj T.toCondensed ≅ Work.ANALYTIC.solidDual T) := by
  obtain ⟨e⟩ := finite_iso_sigma_pt T
  obtain ⟨hC⟩ := CdiscIsoSigmaUnit T
  obtain ⟨h2⟩ := ihomCoprodZ ↥T
  exact ⟨zfreeIsoSigma T e ≪≫ h2.symm ≪≫ ihomPreIso hC⟩

end

end Work.ANALYTIC
