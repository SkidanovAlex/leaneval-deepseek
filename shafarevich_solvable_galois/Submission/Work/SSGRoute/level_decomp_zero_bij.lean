import Submission.Work.SSGRoute.level_zero_from_hom
import Submission.Work.SSGRoute.thetaL0Map_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level decomposition of `Ext^r_G(M, 𝕀_K^S)`

Combining the degree-zero decomposition (`level_zero_from_hom`) with the dimension shift
(`level_decomp_step`) gives the decomposition for all `r`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

variable (R : Set (NK.GlobalCFT.Place K))
  (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)

include R hR

/-- **The degree-zero `Hom`-level decomposition is bijective.** -/
theorem thetaL0Map_bijective (M : Rep.{0,0,0} Coeff (K ≃ₐ[k] K))
    (S : NK.HassePrinciple.GStableSet k K) (hS : S.carrier.Finite) :
    Function.Bijective (thetaL0Map k K R M S) :=
  ⟨thetaL0Map_injective k K R hR M S, thetaL0Map_surjective k K R hR M S hS⟩

/-- **The degree-zero level decomposition is bijective.** -/
theorem level_decomp_bijective_zero (M : Rep.{0,0,0} Coeff (K ≃ₐ[k] K))
    (S : NK.HassePrinciple.GStableSet k K) (hS : S.carrier.Finite) :
    Function.Bijective (thetaL k K R M 0 S) :=
  thetaL_zero_bijective k K R M S (thetaL0Map_bijective k K R hR M S hS)

end

end Work.SSGRoute
