import Mathlib
import Submission.Work.SSGRoute.step4_y_escape_v2.RayClass
import Submission.NK.NUV2.ARL.isOpenNorm
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute

variable {K : Type} [Field K] [NumberField K]

/-- The idèle-class norm subgroup of a finite extension is open (through the openness of the idèlic
norm image and `isOpen_normClassSubgroup_of_isOpen_le`). -/
theorem isOpen_normClassSubgroup' {N : Type} [Field N] [NumberField N] [Algebra K N]
    [FiniteDimensional K N] [IsGalois K N] :
    IsOpen (Idele.normClassSubgroup K N : Set (IdeleClassGroup K)) :=
  NK.NUV2.ArtinBridge.isOpen_normClassSubgroup_of_isOpen_le (Idele.normImage K N)
    (NK.NUV2.ARL.isOpen_normImage_of_isGalois (K := K) (L := N)) le_rfl

/-- The intersection of a finite-index subgroup with a norm class subgroup has finite index. -/
theorem finiteIndex_inf_normClassSubgroup (U : Subgroup (IdeleClassGroup K)) (hU : U.FiniteIndex)
    (N : Type) [Field N] [NumberField N] [Algebra K N] [FiniteDimensional K N] :
    (U ⊓ Idele.normClassSubgroup K N).FiniteIndex := by
  classical
  haveI : U.FiniteIndex := hU
  haveI : (Idele.normClassSubgroup K N).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := N))
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **Čebotarev with the split condition, from the orthogonality.**  Let `U ≤ C_K` be open of finite
index, `N/K` a finite Galois extension, `x ∈ C_K` an element lying in `U · N_{N/K}C_N` (the
*orthogonality*), and `T` a finite set of primes.  Then there is a prime `𝔮 ∉ T` whose idèle class
lies in the norm subgroup (i.e. which **splits completely in `N`**) and with `x · [𝔮] ∈ U`.

The proof is Čebotarev for the subgroup `U ⊓ N_{N/K}C_N`: a prime in the class of `n⁻¹`
(`n` the norm factor of the factorisation `x = u·n`) has both properties at once. -/
theorem chebotarev_split_of_mem_sup (p : ℕ) [Fact p.Prime]
    (U : Subgroup (IdeleClassGroup K)) (hUfin : U.FiniteIndex)
    (hUopen : IsOpen (U : Set (IdeleClassGroup K)))
    (N : Type) [Field N] [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (x : IdeleClassGroup K)
    (horth : x ∈ U ⊔ Idele.normClassSubgroup K N)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    ∃ 𝔮 : NK.Chebotarev.PrimeIdeal K, 𝔮 ∉ T ∧
      IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) ∈ Idele.normClassSubgroup K N ∧
      x * IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) ∈ U := by
  classical
  obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.mp horth
  have hy : n⁻¹ ∈ Idele.normClassSubgroup K N := Subgroup.inv_mem _ hn
  have hxinv : x * n⁻¹ ∈ U := by
    rw [← hun, mul_assoc, mul_inv_cancel, mul_one]
    exact hu
  have hVopen : IsOpen ((U ⊓ Idele.normClassSubgroup K N : Subgroup (IdeleClassGroup K)) :
      Set (IdeleClassGroup K)) :=
    hUopen.inter (isOpen_normClassSubgroup' (K := K) (N := N))
  obtain ⟨𝔮, h𝔮T, h𝔮⟩ := rayClass_chebotarev_v2 (K := K) (U ⊓ Idele.normClassSubgroup K N)
    (finiteIndex_inf_normClassSubgroup U hUfin N) hVopen T
    (QuotientGroup.mk' (U ⊓ Idele.normClassSubgroup K N) n⁻¹)
  have hmem : (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮))⁻¹ * n⁻¹ ∈
      U ⊓ Idele.normClassSubgroup K N := QuotientGroup.eq.mp h𝔮
  have hmem' : IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) * n ∈
      U ⊓ Idele.normClassSubgroup K N := by
    have h := Subgroup.inv_mem _ hmem
    rw [mul_inv_rev, inv_inv, inv_inv] at h
    rwa [mul_comm] at h
  have hqN : IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) ∈
      Idele.normClassSubgroup K N := by
    rw [show IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) =
        (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) * n) * n⁻¹ by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp hmem').2 (Subgroup.inv_mem _ hn)
  refine ⟨𝔮, h𝔮T, hqN, ?_⟩
  have h2 : n * IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) ∈ U := by
    rw [mul_comm]
    exact (Subgroup.mem_inf.mp hmem').1
  rw [show x * IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) =
      (x * n⁻¹) * (n * IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮)) by group]
  exact Subgroup.mul_mem _ hxinv h2

end Work.SSGRoute
