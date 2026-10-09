import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
import Submission.NK.ChebotarevGeneral.exists_isFrobAt_liesOver_of_isFrobAtPrime_under
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ChebotarevGeneral

set_option linter.style.haveILetI false

open IsDedekindDomain

/-- **The fibre of the transfer step is empty when `σ` is not a Frobenius at `𝔭`.**

Let `N/K` be a finite Galois extension of number fields, `M` an intermediate field, `σ ∈ Gal(N/K)`
fixing `M` and `𝔭` a prime of `K`.  If `σ` is not a Frobenius element of `N/K` at `𝔭`, or `𝔭` is
ramified in `N/K`, then there is no prime `𝒬` of `M` above `𝔭` of residue degree one over `𝔭` which
is unramified and at which the image of `σ` in `Gal(N/M)` is a Frobenius element of `N/M`.

Indeed, such a `𝒬` ascends to a prime `P` of `N` above it at which `σ` is a Frobenius element of
`N/K` (`exists_isFrobAt_liesOver_of_isFrobAtPrime_under`), and the primes above `𝔭` are
unramified because `𝒬`'s prime below it is; both conclusions contradict the hypothesis. -/
theorem card_fibre_frobSetSub_eq_zero_of_not {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    {𝔭 : NK.Chebotarev.PrimeIdeal K}
    (hnot : ¬ (NK.Chebotarev.IsFrobAtPrime (K := K) (L := N) 𝔭 σ ∧
      NK.ChebotarevGeneral.IsUnramifiedAt (K := K) (N := N) 𝔭)) :
    Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal ↥M //
        NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
        (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
        NK.ChebotarevGeneral.IsUnramifiedAt (K := K) (N := N)
          (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) ∧
        𝒬.asIdeal.LiesOver 𝔭.asIdeal} = 0 := by
  classical
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun x => ?_⟩
  obtain ⟨𝒬, hfrob, hfdeg, hunr, hQ⟩ := x
  -- the residue degree of `𝒬` over `𝔭` is one
  have hf : 𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1 := by
    rw [(Ideal.liesOver_iff 𝒬.asIdeal 𝔭.asIdeal).mp hQ]
    exact hfdeg
  -- ascent: a prime `P` of `N` above `𝒬` at which `σ` is a Frobenius element of `N/K`
  obtain ⟨P, hPQ, hPfrob⟩ :=
    exists_isFrobAt_liesOver_of_isFrobAtPrime_under (K := K) (N := N) M hQ hf hσ hfrob
  refine hnot ⟨⟨P, ?_, hPfrob⟩, ?_⟩
  · haveI := hPQ
    haveI := hQ
    exact Ideal.LiesOver.trans P.asIdeal 𝒬.asIdeal 𝔭.asIdeal
  · rw [IsUnramifiedAt]
    intro P' hP'
    refine hunr P' ?_
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact (Ideal.liesOver_iff 𝒬.asIdeal 𝔭.asIdeal).mp hQ ▸ hP'

end NK.ChebotarevGeneral
