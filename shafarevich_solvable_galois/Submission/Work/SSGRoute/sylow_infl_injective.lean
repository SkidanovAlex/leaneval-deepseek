import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.bridgeE_map
import Submission.Work.SSGRoute.classIncl_inflation_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of the level inflation on `H²`, in the `Ext` core

`Work.SSGRoute.SylowLevel.inflCIn_injective`: for finite Galois levels `K ≤ L ≤ L'` of a fixed
algebraically closed `Ω`, the level inflation
`inflCIn : H²(Gal(L/k), C_L) → H²(Gal(L'/k), C_{L'})` is injective.

This is the `Ext`-core form of `Work.SSGRoute.classIncl_inflation_injective` (the group-cohomology
statement, proved in `classIncl_inflation_injective.lean` from the five-term sequence and
`H¹(Gal(L'/L), C_{L'}) = 0`); the transport to `Ext` uses the naturality of the `E0b` bridge under a
change of group together with a coefficient map, `Work.SSGRoute.bridgeE_map`
(`Submission/Work/SSGRoute/bridgeE_map.lean`).  The derivation is the same one as Step 4 of
`Work.SSGRoute.phi0_family_vanish_of_local`.
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute
namespace SylowLevel

open SSGRoute.PTExt CategoryTheory

/-- **Injectivity of the level inflation on `H²`.** -/
theorem inflCIn_injective {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (L L' : IntermediateField K Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (hLL : L ≤ L') :
    Function.Injective (fun y : extH (classesK k L) 2 => inflCIn (k := k) hLL y) := by
  intro y y' hyy'
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hg := classIncl_inflation_injective k ↥L ↥L'
  have hsquare : ∀ y : extH (classesK k L) 2,
      bridgeE (↥L' ≃ₐ[k] ↥L') (classesK k L') 2
          ((groupCohomology.map (galRes k L L') (classIncl k L L') 2).hom
            ((bridgeE (↥L ≃ₐ[k] ↥L) (classesK k L) 2).symm y)) = inflCIn (k := k) hLL y := by
    intro y
    rw [bridgeE_map (galRes k L L') (classesK k L) (classesK k L') (classIncl k L L') 2,
      AddEquiv.apply_symm_apply]
    rfl
  have hyy'b : inflCIn (k := k) hLL y = inflCIn (k := k) hLL y' := hyy'
  have h1 : (groupCohomology.map (galRes k L L') (classIncl k L L') 2).hom
      ((bridgeE (↥L ≃ₐ[k] ↥L) (classesK k L) 2).symm y)
      = (groupCohomology.map (galRes k L L') (classIncl k L L') 2).hom
        ((bridgeE (↥L ≃ₐ[k] ↥L) (classesK k L) 2).symm y') := by
    apply (bridgeE (↥L' ≃ₐ[k] ↥L') (classesK k L') 2).injective
    exact (hsquare y).trans (hyy'b.trans (hsquare y').symm)
  exact (bridgeE (↥L ≃ₐ[k] ↥L) (classesK k L) 2).symm.injective (hg h1)

end SylowLevel
end Work.SSGRoute
