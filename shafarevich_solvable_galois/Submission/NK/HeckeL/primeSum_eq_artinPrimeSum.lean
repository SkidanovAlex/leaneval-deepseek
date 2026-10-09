import Mathlib
import Submission.NK.HeckeL.Dictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL

theorem primeSum_eq_artinPrimeSum {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U) (s : ℝ) :
    NK.HeckeL.primeSum K U S χ s =
      NK.HeckeL.artinPrimeSum K L S (NK.HeckeL.rayCharEquivGalois h e χ) s := by
  simp only [primeSum, artinPrimeSum]
  refine tsum_congr fun 𝔭 => ?_
  have h1 : (reciprocityEquiv h e).symm (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1)
      = primeClass K U 𝔭.1 := by
    rw [← hFrob.iso_primeClass 𝔭.1 𝔭.2, reciprocityEquiv, MulEquiv.symm_apply_apply]
  simp only [rayCharEquivGalois_apply_apply, h1, RayChar.atPrime]

end NK.HeckeL
