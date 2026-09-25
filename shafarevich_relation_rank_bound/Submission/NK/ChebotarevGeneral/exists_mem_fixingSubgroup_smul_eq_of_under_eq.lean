import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
import Submission.NK.ChebotarevGeneral.card_isFrobAt_liesOver_mul_orderOf

namespace NK.ChebotarevGeneral

open NK.Chebotarev

noncomputable section

section Action

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **The two actions on the primes of `𝓞 N` agree under `M.fixingSubgroupEquiv`.**

The action of `Gal(N/K)` on the finite places of `N` (`NK.Chebotarev.instSMulPrimeIdeal`)
restricts, along the isomorphism `M.fixingSubgroupEquiv : Gal(N/M) ≃* M.fixingSubgroup`, to the
action of `Gal(N/M)`.  Both are given by transporting a prime ideal along the restriction of the
same field automorphism to `𝓞 N`, so the two `galRestrict` maps agree. -/
theorem smul_primeIdeal_fixingSubgroupEquiv_symm (M : IntermediateField K N) (τ : Gal(N/↥M))
    (P : PrimeIdeal N) :
    ((M.fixingSubgroupEquiv.symm τ : M.fixingSubgroup) : Gal(N/K)) • P = τ • P := by
  set σK : Gal(N/K) := ((M.fixingSubgroupEquiv.symm τ : M.fixingSubgroup) : Gal(N/K)) with hσK
  have hfun : (galRestrict (NumberField.RingOfIntegers K) K N (NumberField.RingOfIntegers N) σK :
        NumberField.RingOfIntegers N →+* NumberField.RingOfIntegers N) =
      (galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N) τ :
        NumberField.RingOfIntegers N →+* NumberField.RingOfIntegers N) := by
    ext x
    show algebraMap (NumberField.RingOfIntegers N) N
          (galRestrict (NumberField.RingOfIntegers K) K N (NumberField.RingOfIntegers N) σK x)
        = algebraMap (NumberField.RingOfIntegers N) N
          (galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N) τ x)
    rw [algebraMap_galRestrict_apply (A := NumberField.RingOfIntegers K) (K := K)
          (B := NumberField.RingOfIntegers N) σK x,
        algebraMap_galRestrict_apply (A := NumberField.RingOfIntegers ↥M) (K := ↥M)
          (B := NumberField.RingOfIntegers N) τ x]
    rfl
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [smul_primeIdeal_asIdeal, smul_primeIdeal_asIdeal, hfun]

end Action

/-- **Primes of `N` above a prime of an intermediate field are conjugate under `Gal(N/M)`.**

Let `N/K` be a finite Galois extension of number fields and `M` an intermediate field.  If two
primes `P`, `P'` of `𝓞 N` lie over the same prime of `𝓞 M`, then `P'` is the image of `P` under an
element of `Gal(N/M)` (acting through `NK.Chebotarev.instSMulPrimeIdeal`). -/
theorem exists_mem_fixingSubgroup_smul_eq_of_under_eq {K N : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    {M : IntermediateField K N} {P P' : NK.Chebotarev.PrimeIdeal N}
    (h : P.under (NumberField.RingOfIntegers ↥M) = P'.under (NumberField.RingOfIntegers ↥M)) :
    ∃ h : M.fixingSubgroup,
      (h : Gal(N/K)) • P = P' := by
  have hP : P.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers ↥M)).asIdeal :=
    Ideal.over_under (A := NumberField.RingOfIntegers ↥M) P.asIdeal
  have hP' : P'.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers ↥M)).asIdeal := by
    rw [h]
    exact Ideal.over_under (A := NumberField.RingOfIntegers ↥M) P'.asIdeal
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_liesOver (K := ↥M) (N := N)
    (𝔭 := P.under (NumberField.RingOfIntegers ↥M)) hP hP'
  exact ⟨M.fixingSubgroupEquiv.symm τ,
    by rw [smul_primeIdeal_fixingSubgroupEquiv_symm M τ P, hτ]⟩

end

end NK.ChebotarevGeneral
