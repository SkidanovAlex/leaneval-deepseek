import Mathlib
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
import Submission.Work.SSG8Escape.correction_ssg8
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Gal(M/↥K)` has exponent `p` for the class field `M` of `U_p = gesU ⊔ (p-th powers)`

The class field `M` of `U_p ⊇ (C_↥K)^p` has `C_↥K/U_p` of exponent `p`; via the idèlic Artin map
(whose surjectivity is Chebotarev's density theorem, from the Frobenius normalisation `hfrob`)
`Gal(M/↥K) ≅ C_↥K/U_p`, so `Gal(M/↥K)` has exponent `p` as well.  This is the input which makes
the characters `A →* Multiplicative (ZMod p)` separate points of `Gal(M/↥K)`
(`Work.SSGRoute.N2v2.mem_of_forall_monoidHom_eq_one`).
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

/-- **The idèlic Artin map of `M/↥K` is surjective** (Chebotarev, from the Frobenius
normalisation). -/
theorem range_art_eq_top (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (art : Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮) :
    art.range = ⊤ := by
  classical
  have hcomm : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  obtain ⟨m, hm, hram, _hprinc⟩ := NK.CFTLib.artinReciprocityIdeal_proved ↥K ↥M hcomm
  refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := ↥K) (L := ↥M)
    (NK.CFTLib.Arl.primesDividing (K := ↥K) m hm) art.range ?_
  intro 𝔭 h𝔭 σ hσ
  have hpm : (m : 𝓞 ↥K) ∉ 𝔭.asIdeal :=
    fun h => h𝔭 ((NK.CFTLib.Arl.mem_primesDividing (K := ↥K) m hm 𝔭).mpr h)
  have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔭 :=
    (NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one
      (K := ↥K) (L := ↥M) 𝔭).mpr (hram 𝔭 hpm)
  have hσeq : σ = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔭 :=
    (NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := ↥K) (L := ↥M) hcomm 𝔭 hunr).unique hσ
      (NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭 hunr)
  rw [hσeq, ← hfrob 𝔭 hunr]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

/-- **`Gal(M/↥K)` has exponent `p`.** -/
theorem gal_pow_eq_one (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : Idele.normClassSubgroup ↥K ↥M = SSG8Escape.gesUPow ↥K p T')
    (art : Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = Idele.normImage ↥K ↥M ⊔ Idele.principalSubgroup ↥K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime ↥K 𝔮) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮)
    (σ : ↥M ≃ₐ[↥K] ↥M) : σ ^ p = 1 := by
  classical
  have hsurj := range_art_eq_top p K T' M art hfrob
  obtain ⟨x, hx⟩ : σ ∈ art.range := by rw [hsurj]; exact Subgroup.mem_top σ
  rw [← hx, ← map_pow]
  change art (x ^ p) = 1
  rw [← MonoidHom.mem_ker, hker]
  -- `x ^ p` lies in the norm class subgroup, hence in the kernel of `art`
  have hmem : IdeleClassGroup.mk ↥K (x ^ p) ∈ SSG8Escape.gesUPow ↥K p T' := by
    rw [Work.SSG8Escape.gesUPow_eq]
    refine Subgroup.mem_sup_right ?_
    rw [map_pow]
    exact Work.SSGRoute.EscapeCoreLib.pow_mem_pPowSubgroup _
  rw [← hM] at hmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  have hp' : y⁻¹ * x ^ p ∈ Idele.principalSubgroup ↥K := IdeleClassGroup.mk_eq_mk_iff.mp hyx
  obtain ⟨δ, hδ⟩ := Idele.mem_principalSubgroup.mp hp'
  have hδmem : Idele.principalIdele ↥K δ ∈ Idele.principalSubgroup ↥K :=
    Idele.mem_principalSubgroup.mpr ⟨δ, rfl⟩
  have hxp : x ^ p = y * Idele.principalIdele ↥K δ := by rw [hδ]; group
  rw [hxp]
  exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hδmem)

end Work.SSGRoute.N2v2
