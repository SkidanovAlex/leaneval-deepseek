import Mathlib
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
import Submission.Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime
import Submission.Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
import Submission.Work.SSGRoute.H9.lPinned_eq_kummerPinnedValue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

theorem value_eq_of_pinned {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α : (↥K)ˣ)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L A)
    (hker : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0)
    (hkill : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    (gt : Ω ≃ₐ[k] Ω) (hgt : gt ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (SSGRoute.res k L gt))
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hpin : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α gt
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ψ :=
  Work.SSGRoute.H9.lPinned_eq_kummerPinnedValue ζ hζ hζK α L A hA 𝔭 h𝔭 hunrL hker hkill gt ψ
    hgt hψ hfrob hpin

end Work.SSGRoute.NodeS37
