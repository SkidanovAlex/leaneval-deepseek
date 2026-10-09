import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver
import Submission.NK.Chebotarev.LFunctions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Prime-level transfer compatibility of Frobenius elements

In a tower `K ⊆ E ⊆ L ⊆ M` of number fields with `M/K` Galois and `L/K` abelian, the restriction
to `L` of the Frobenius at a prime `𝔮` of `E` (for the extension `M/E`) is the
`f(𝔮|𝔭)`-th power of the Frobenius at `𝔭 = 𝔮 ∩ K` (for `L/K`):

  `Frob_𝔮(M/E)|_L = Frob_𝔭(L/K)^{f(𝔮|𝔭)}`.

This is the prime-level input of the norm/restriction transfer of Lang, *Algebraic Number Theory*,
Ch. X §2, Theorem 2 (`N_{E/K}(𝔮) = 𝔭^{f(𝔮|𝔭)}`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **Prime-level transfer compatibility of Frobenius elements.**  In a tower `K ⊆ E ⊆ L ⊆ M` of
number fields with `M/K` Galois and `L/K` abelian, the restriction to `L` of the Frobenius at a
prime `𝔮` of `E` (for the extension `M/E`) is the `f(𝔮|𝔭)`-th power of the Frobenius at
`𝔭 = 𝔮 ∩ K` (for `L/K`). -/
theorem restrictNormalHom_frobAtPrime_eq_pow {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E L : IntermediateField K M) [FiniteDimensional K ↥E] [FiniteDimensional K ↥L]
    [IsGalois K ↥L]
    (hcomm : ∀ a b : ↥L ≃ₐ[K] ↥L, a * b = b * a)
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥E) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (h𝔮 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal)
    (hunr : ∀ Q : NK.Chebotarev.PrimeIdeal ↥L, Q.asIdeal.LiesOver 𝔭.asIdeal →
      Q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
      (AlgEquiv.restrictScalars K (NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮))
      = (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) 𝔭) ^
          (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
  have hfrob : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) 𝔭
      (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) 𝔭) :=
    NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭 hunr
  obtain ⟨Q₀, hQ₀, hFQ₀⟩ := hfrob
  have hg : ∀ Q : NK.Chebotarev.PrimeIdeal ↥L, Q.asIdeal.LiesOver 𝔭.asIdeal →
      NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) Q
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) 𝔭) :=
    fun Q hQ => NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver hcomm hQ₀ hQ hFQ₀
  have h := NK.CFTLib.Arl.frobAtPrime_restrict_eq_pow (K := K) (E := M) E L 𝔭 hunr
    (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) 𝔭) hg 𝔮 h𝔮
  rw [NK.CFTLib.Arl.restrictGalEquiv_apply] at h
  exact h

end NK.CFTLib.ArtinReciprocityIdeal
