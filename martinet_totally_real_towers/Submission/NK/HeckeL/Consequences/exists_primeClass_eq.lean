import Mathlib
import Submission.NK.HeckeL.Dictionary
import Submission.NK.HeckeL.Consequences.abelianLFunctions
import Submission.NK.HeckeL.Consequences.exists_prime_isFrobAtPrime_outside

namespace NK.HeckeL.Consequences

/-- **Čebotarev: every class in the ray class group is the class of a prime outside any
prescribed finite set.**

Continuing `exists_prime_isFrobAtPrime_outside`: the Frobenius at an unramified prime `𝔭` and the
class of `𝔭` in the ray class group correspond under Artin reciprocity
(`NK.HeckeL.FrobeniusCompatibility.iso_primeClass`).  Hence prescribing a class `c` in the ray
class group is the same as prescribing the Frobenius `(reciprocityEquiv hrec e) c`, and Čebotarev
supplies a prime realising it outside `T ∪ S`. -/
theorem exists_primeClass_eq {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (hrec : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U hrec e S)
    (hA : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)
    (T : Finset (NK.HeckeL.PrimeIdeal K)) :
    ∃ 𝔭 : NK.HeckeL.PrimeIdeal K,
      𝔭 ∉ S ∧ 𝔭 ∉ T ∧ NK.HeckeL.primeClass K U 𝔭 = c := by
  classical
  obtain ⟨𝔭, h𝔭TS, h𝔭Frob⟩ :=
    NK.HeckeL.Consequences.exists_prime_isFrobAtPrime_outside S hcomm hS hA
      ((NK.HeckeL.reciprocityEquiv hrec e) c) (T ∪ S)
  have h𝔭S : 𝔭 ∉ S := fun h => h𝔭TS (Finset.mem_union_right T h)
  have h𝔭T : 𝔭 ∉ T := fun h => h𝔭TS (Finset.mem_union_left S h)
  refine ⟨𝔭, h𝔭S, h𝔭T, ?_⟩
  -- `𝔭` is unramified, hence the Frobenius at `𝔭` is the prescribed element
  have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 := by
    by_contra h
    exact h𝔭S (hS 𝔭 h)
  have hfrob : NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 =
      (NK.HeckeL.reciprocityEquiv hrec e) c :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔭 hunr _).mp h𝔭Frob
  refine (e.trans hrec.iso).injective ?_
  rw [hFrob.iso_primeClass 𝔭 h𝔭S]
  exact hfrob

end NK.HeckeL.Consequences
