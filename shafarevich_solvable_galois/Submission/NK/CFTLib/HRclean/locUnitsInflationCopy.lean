import Mathlib
import Submission.NK.CFTLib.HRclean.ARLClean
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# CLEAN COPY (agent H-): localisation of the level inflation, and the identity
`inflation = unitsLevelMapTower`

A copy of
`Submission/Work/CFTLib/IdeleHasse/Descent/locUnits_inflation_eq_zero_of_loc_eq_zero.lean`
with `NK.CFTLib.HRclean.ARL.TransferSupport` replaced by the clean copy in this directory (see
`Submission/Work/CFTLib/HRclean/README.md`).  Statements and proofs are unchanged.
-/

/-!
# The localisation of an inflated classes vanishes where the localisation vanishes

Let `K ⊆ L ⊆ E` be a tower of number fields with `L/K` and `E/K` Galois, let
`c ∈ H²(Gal(L/K), Lˣ)`, and let `ŵ` be a place of `E` lying over the place `v'` of `L`.  If the
localisation of `c` at `v'` vanishes, then the localisation at `ŵ` of the inflation of `c`
(the level change `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)`) vanishes as well.

This is the compatibility of the relative Hasse–Brauer–Noether localisations
`NK.HassePrinciple.locUnits` with the level change, in the form in which the Brauer transfer
consumes it.  It is *purely formal*: the level change `NK.CFTLib.HRclean.ARL.inflation` agrees with the
tower level map `NK.NUV2.LC.unitsLevelMapTower` of `LocalLevelSystem`, and for the latter the
statement is `NK.NUV2.LC.RouteB.locUnits_tower_eq_zero`, which is the naturality square of the
localisations in the tower.

* `restrictHom_eq_restrictNormalHom`: the restriction map `Gal(E/K) →* Gal(L/K)` of
  `TransferSupport` (defined through the image field of `L` in `E`) is Mathlib's
  `AlgEquiv.restrictNormalHom`; both are determined by `algebraMap L E ∘ · = · ∘ algebraMap L E`.
* `inflation_eq_unitsLevelMapTower`: consequently the two level changes coincide.
-/

open CategoryTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.CFTLib.HRclean.DescentInf

section Helpers

variable {K L E : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field E]
  [NumberField E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

/-- **The restriction map of `TransferSupport` is Mathlib's `restrictNormalHom`.**  Both send
`σ : Gal(E/K)` to the unique `K`-automorphism of `L` whose image in `E` is `σ` restricted to the
image of `L`, i.e. both satisfy `algebraMap L E (ρ σ y) = σ (algebraMap L E y)`. -/
theorem restrictHom_eq_restrictNormalHom [IsGalois K L] :
    NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E)
      = AlgEquiv.restrictNormalHom (K₁ := E) (E := L) := by
  ext σ y
  apply (algebraMap L E).injective
  rw [NK.CFTLib.HRclean.ARL.restrictHom_apply_coe]
  exact (AlgEquiv.restrictNormal_commutes σ L y).symm

/-- The tower coefficient map `Lˣ → Eˣ` of `TransferSupport` and the one of `LocalLevelSystem`
are the same linear map (both are `Units.map (algebraMap L E)`). -/
theorem unitsInclRep_hom_eq [IsGalois K L] :
    (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E)).hom.toLinearMap
      = (NK.NUV2.LC.unitsInclTowerCoeff (F := K) (L := L) (M := E)).hom.toLinearMap :=
  rfl

/-- **The level change of `TransferSupport` is the tower level map of `LocalLevelSystem`**: the
inflation `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)` along the restriction of the Galois groups and the
units inclusion `Lˣ → Eˣ`. -/
theorem inflation_eq_unitsLevelMapTower [IsGalois K L] :
    NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)
      = NK.NUV2.LC.unitsLevelMapTower (F := K) (L := L) (M := E) := by
  rw [NK.CFTLib.HRclean.ARL.inflation, NK.NUV2.LC.unitsLevelMapTower]
  exact groupCohomology.map_congr (restrictHom_eq_restrictNormalHom (K := K) (L := L) (E := E))
    (unitsInclRep_hom_eq (K := K) (L := L) (E := E)) 2

end Helpers

theorem locUnits_inflation_eq_zero_of_loc_eq_zero {K L E : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field E] [NumberField E] [Algebra K L] [Algebra K E]
    [Algebra L E] [IsScalarTower K L E] [FiniteDimensional K L] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K E]
    (c : groupCohomology (NK.HassePrinciple.unitsRep K L) 2)
    (v' : NK.GlobalCFT.Place L) (ŵ : NK.GlobalCFT.Place E)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v')
    (hc : (NK.HassePrinciple.locUnits K L v').hom c = 0) :
    (NK.HassePrinciple.locUnits K E ŵ).hom
      ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom c) = 0 := by
  have hinf : ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom c)
      = ((NK.NUV2.LC.unitsLevelMapTower (F := K) (L := L) (M := E)).hom c) := by
    rw [inflation_eq_unitsLevelMapTower (K := K) (L := L) (E := E)]
  rw [hinf]
  exact NK.NUV2.LC.RouteB.locUnits_tower_eq_zero (F := K) (L := L) (M := E) c hv hc

end NK.CFTLib.HRclean.DescentInf
