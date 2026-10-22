import Mathlib
import Submission.Work.ANALYTIC.Basic
import Submission.Work.TOOLKIT.Instances

/-!
# The free discrete light condensed abelian group on `J` is a coproduct of copies of `ℤ`

The main result of this file is

`disc_finsupp_iso_coprod (J : Type) :
  Nonempty (Iso ((discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ (J →₀ ℤ))) (∐ (fun _ : J => Z)))`

i.e. the discrete light condensed abelian group on the free abelian group `ℤ[J] = J →₀ ℤ`
is (isomorphic to) the coproduct over `J` of the discrete light condensed abelian group `ℤ`.

The argument is purely formal, and has two halves.

* In `ModuleCat ℤ` the free module `J →₀ ℤ` *is* the coproduct of `J` copies of `ℤ`
  (`ModuleCat.finsuppCoconeIsColimit`), giving the isomorphism `finsuppIsoCoproductZ` below.
* The discrete functor `LightCondensed.discrete (ModuleCat ℤ) = constantSheaf _ _` is a left
  adjoint (its right adjoint is the evaluation at a point, `LightCondensed.underlying`), hence
  preserves coproducts: `PreservesCoproduct.iso`.

Composing the two gives the claim, since `Z` *is by definition*
`(LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)`.

Everything here is `sorry`-free; the only imported ingredients are Mathlib and the coproduct
instances for `LightCondAb` from `Submission.Work.TOOLKIT.Instances`.
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

namespace Work.ANALYTIC

universe u

/-! ## The discrete functor is a left adjoint, hence preserves coproducts -/

/-- The discrete functor on `ℤ`-modules is left adjoint to the "underlying" functor (evaluation at
a point), so it is a left adjoint.  Registering this as an instance makes Mathlib's
`PreservesColimit`-instances available for it, in particular for coproduct shapes. -/
instance instDiscreteIsLeftAdjoint : (LightCondensed.discrete (ModuleCat ℤ)).IsLeftAdjoint :=
  (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).isLeftAdjoint

/-- For a family `f : J → ModuleCat ℤ`, the discrete light condensed abelian group on the
coproduct `∐ f` is the coproduct of the discrete light condensed abelian groups on the summands.
This is `PreservesCoproduct.iso` for the left adjoint `LightCondensed.discrete (ModuleCat ℤ)`. -/
def discreteCoprodIso {J : Type} (f : J → ModuleCat ℤ) :
    (LightCondensed.discrete (ModuleCat ℤ)).obj (∐ f) ≅
      ∐ fun j => (LightCondensed.discrete (ModuleCat ℤ)).obj (f j) :=
  PreservesCoproduct.iso _ f

/-! ## The free `ℤ`-module on `J` is the coproduct of `J` copies of `ℤ` -/

/-- The coproduct in `ModuleCat ℤ` of `J` copies of `ℤ` is the free module `J →₀ ℤ`: the concrete
coproduct cone `ModuleCat.finsuppCocone ℤ ℤ J` (with point `↧(J →₀ ℤ)` and inclusions
`Finsupp.lsingle`) is colimiting, hence its point is the coproduct. -/
def finsuppIsoCoproductZ (J : Type) :
    ModuleCat.of ℤ (J →₀ ℤ) ≅ ∐ (fun _ : J => ModuleCat.of ℤ ℤ) :=
  (ModuleCat.finsuppCoconeIsColimit ℤ ℤ J).coconePointUniqueUpToIso (coproductIsCoproduct _)

/-! ## The main statement -/

/-- The discrete light condensed abelian group on the free abelian group `J →₀ ℤ` is the
coproduct over `J` of the discrete light condensed abelian group `ℤ`.

Indeed `ℤ[J] = J →₀ ℤ` is the coproduct of `J` copies of `ℤ` in `ModuleCat ℤ`
(`finsuppIsoCoproductZ`), and the discrete functor, being a left adjoint, preserves coproducts
(`discreteCoprodIso`). -/
theorem disc_finsupp_iso_coprod (J : Type) :
    Nonempty (CategoryTheory.Iso
      ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ (J →₀ ℤ)))
      (∐ (fun _ : J => Work.ANALYTIC.Z))) :=
  ⟨(LightCondensed.discrete (ModuleCat ℤ)).mapIso (finsuppIsoCoproductZ J) ≪≫
    discreteCoprodIso (fun _ : J => ModuleCat.of ℤ ℤ)⟩

end Work.ANALYTIC
