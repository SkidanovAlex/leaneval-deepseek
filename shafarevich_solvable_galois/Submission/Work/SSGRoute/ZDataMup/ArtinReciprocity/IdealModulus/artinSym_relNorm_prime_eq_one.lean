import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.NKImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem artinSym_relNorm_prime_eq_one
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (𝔮 : NK.Chebotarev.PrimeIdeal L)
    (hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L)
      (𝔮.under (NumberField.RingOfIntegers K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      ((Ideal.relNorm (NumberField.RingOfIntegers K) 𝔮.asIdeal :
          Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = 1 := by
  haveI : 𝔮.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime 𝔮.ne_bot 𝔮.isPrime
  have hqne : (𝔮.under (𝓞 K)).asIdeal ≠ ⊥ := by
    rw [HeightOneSpectrum.under_asIdeal]
    exact Ideal.under_ne_bot (𝓞 K) 𝔮.ne_bot
  haveI : ((𝔮.under (𝓞 K)).asIdeal).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hqne inferInstance
  haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
    ⟨HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
  have hrelNorm : Ideal.relNorm (𝓞 K) 𝔮.asIdeal
      = (𝔮.under (𝓞 K)).asIdeal ^ 𝔮.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.relNorm_eq_pow_of_isMaximal 𝔮.asIdeal ((𝔮.under (𝓞 K)).asIdeal)
  rw [hrelNorm, FractionalIdeal.coeIdeal_pow,
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_pow hcomm
      (FractionalIdeal.coeIdeal_ne_zero.mpr hqne) (𝔮.asIdeal.inertiaDeg (𝓞 K)),
    NK.CFTLib.Arl.artinSym_prime hcomm (𝔮.under (𝓞 K)),
    ← orderOf_dvd_iff_pow_eq_one,
    NK.CFTLib.ArtinReciprocityIdeal.orderOf_frobAtPrime_eq_inertiaDeg (𝔮.under (𝓞 K)) 𝔮
      (Ideal.LiesOver.mk (HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮)) hunr]

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
