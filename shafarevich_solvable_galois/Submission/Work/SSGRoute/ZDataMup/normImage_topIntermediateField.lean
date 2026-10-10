import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

/-- **Transport of the idèlic norm subgroup along a compatible pair of ring equivalences.**
For a compatible pair of ring equivalences `eK : K ≃+* K'`, `eL : L ≃+* L'` of number fields
(`hcomp : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)`), the idèle transport
`ideleEquiv eK : 𝕀 K ≃* 𝕀 K'` carries the norm subgroup `N_{L/K} 𝕀 L` onto `N_{L'/K'} 𝕀 L'`. -/
theorem normImage_map_ideleEquiv {K L K' L' : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [Field K'] [NumberField K']
    [Field L'] [NumberField L'] [Algebra K' L'] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (NK.GlobalCFT.Idele.normImage K L).map
        (NK.GlobalCFTdeep.Transport.ideleEquiv eK).toMonoidHom =
      NK.GlobalCFT.Idele.normImage K' L' := by
  rw [NK.GlobalCFT.Idele.normImage_eq_map K L, NK.GlobalCFT.Idele.normImage_eq_map K' L']
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨NK.GlobalCFTdeep.Transport.ideleEquiv eL a,
      (NK.GlobalCFTdeep.Transport.ideleEquiv_normIdeleHom eK eL hcomp a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨NK.GlobalCFT.Idele.normIdeleHom K L
      ((NK.GlobalCFTdeep.Transport.ideleEquiv eL).symm b), ⟨_, rfl⟩, ?_⟩
    simpa using NK.GlobalCFTdeep.Transport.ideleEquiv_normIdeleHom eK eL hcomp
      ((NK.GlobalCFTdeep.Transport.ideleEquiv eL).symm b)

theorem normImage_topIntermediateField {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    NK.GlobalCFT.Idele.normImage K ↥(⊤ : IntermediateField K L) =
      NK.GlobalCFT.Idele.normImage K L := by
  let e : L ≃ₐ[K] ↥(⊤ : IntermediateField K L) := IntermediateField.topEquiv.symm
  have h1 := normImage_map_ideleEquiv (K := K) (L := L) (K' := K) (L' := L)
    (RingEquiv.refl K) (RingEquiv.refl L) (fun x => rfl)
  have h2 := normImage_map_ideleEquiv (K := K) (L := L)
    (K' := K) (L' := ↥(⊤ : IntermediateField K L))
    (RingEquiv.refl K) e.toRingEquiv (fun x => by simpa using e.commutes x)
  exact h2.symm.trans h1

end Work.SSGRoute.ZDataMup
