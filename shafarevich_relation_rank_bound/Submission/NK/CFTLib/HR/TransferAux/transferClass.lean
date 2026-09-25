import Mathlib
import Submission.NK.CFTLib.HR.TransferAux.Defs
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT CategoryTheory
open scoped NumberField

namespace NK.CFTLib.HR.TransferAux

open IsDedekindDomain IdeleHasse

attribute [local instance 5000] Rep.hV1 Rep.hV2

theorem transferClass {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M]
    [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ (y : Kˣ),
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        NK.CFTLib.IdeleHasse.localImageAt v y ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀)
    (x : Kˣ)
    (hx : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : NK.GlobalCFT.Place M, NK.GlobalCFT.Place.LiesOver w v₀ →
      Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w)
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) :
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x = 0 := by sorry

end NK.CFTLib.HR.TransferAux
