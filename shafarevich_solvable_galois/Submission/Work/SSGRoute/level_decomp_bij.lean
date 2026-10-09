import Submission.Work.SSGRoute.level_decomp_zero_bij
import Submission.Work.SSGRoute.level_decomp_step
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level decomposition of `Ext^r_G(M, 𝕀_K^S)` in all degrees
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

/-- **The level decomposition in degree `r`**: localisation at a transversal of the
`Gal(K/k)`-orbits identifies `Ext^r_G(M, 𝕀_K^S)` with the product of the local groups. -/
theorem level_decomp_bijective (M : Rep.{0,0,0} Coeff (K ≃ₐ[k] K)) (r : ℕ)
    (S : NK.HassePrinciple.GStableSet k K) (hS : S.carrier.Finite) :
    Function.Bijective (thetaL k K R M r S) :=
  level_decomp_step k K R hR
    (fun M S hS => level_decomp_bijective_zero k K R hR M S hS) M r S hS

end

end Work.SSGRoute
