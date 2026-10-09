import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.HR.TransferAux.Defs
import Submission.NK.CFTLib.HR.TransferAux.FinalStep
import Submission.NK.CFTLib.HR.TransferAux.transferClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT

namespace NK.CFTLib.HR

theorem transferAt {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L]
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
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ :=
  NK.CFTLib.HR.TransferAux.finalStep hcycL x v₀
    (fun g hg => NK.CFTLib.HR.TransferAux.transferClass hgen hcycL hcycM v₀ hM x hx hv₀ g hg)

end NK.CFTLib.HR
