import Mathlib
import Submission.Work.SSG8Escape.artin_reduces_to_local_product
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

theorem artinFixes_localFactors_two
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    [IsMulCommutative (↥F ≃ₐ[↥K] ↥F)]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (p := 2) (K' := Ω) c ≤ F)
    (χ : (↥F ≃ₐ[↥K] ↥F) →* Multiplicative (ZMod 2))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom F σ) =
        Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ))
    (a : (↥K)ˣ) (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hLT : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hΦprin : ∀ x : (↥K)ˣ, Φ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1)
    (hΦnorm : ∀ y : NK.GlobalCFT.Idele ↥F, Φ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1)
    (harch : ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) a ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
          (NK.GlobalCFT.Place.ofInfinite w))
    (hTfix : (∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1) :
    χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 :=
  Work.SSGRoute.ZDataTwo.artinFixes_localFactors_two_aux (k := k) (Ω := Ω)
    K ζ hζ F c hc χ hχ a T' hLT Φ hΦprin hΦnorm harch hTfix

end Work.SSGRoute.ZDataTwo
