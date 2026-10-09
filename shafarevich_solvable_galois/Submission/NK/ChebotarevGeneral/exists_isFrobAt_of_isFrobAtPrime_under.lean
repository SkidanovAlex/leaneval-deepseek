import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Ascent of a Frobenius element from an intermediate field

Let `N/K` be a finite Galois extension of number fields and `M` an intermediate field.  Let
`σ ∈ Gal(N/K)` fix `M` pointwise and let `𝒬` be a prime of `𝓞 M` lying over a prime `𝔭` of `𝓞 K`
with residue degree one over `𝔭`.  If the image of `σ` in `Gal(N/M)` is a Frobenius element at
`𝒬` for the extension `N/M`, then `σ` is a Frobenius element for the extension `N/K` at some
prime `P` of `𝓞 N` above `𝔭`.

The proof is the naive one: the witness for `IsFrobAtPrime (K := ↥M) (L := N) 𝒬 τ` is a prime `P`
of `𝓞 N` above `𝒬` (hence above `𝔭`), and since `τ` and `σ` induce the same automorphism of `𝓞 N`
while the residue cardinalities `#(𝓞 M ⧸ 𝒬) = #(𝓞 K ⧸ 𝔭)` agree because the residue degree is one,
the defining congruence for the Frobenius over `K` follows from the one over `M`.

The residue cardinality comparison is `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver`.
-/

namespace NK.ChebotarevGeneral

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open IsDedekindDomain

/-- **Ascent of a Frobenius element from an intermediate field.**  Let `M` be an intermediate field
of `N/K`, `σ ∈ Gal(N/K)` fixing `M` pointwise, and let `𝒬` be a prime of `𝓞 M` lying over `𝔭` with
residue degree one over `𝔭`.  If the image of `σ` in `Gal(N/M)` is a Frobenius element at `𝒬` (in
the extension `N/M`), then `σ` is a Frobenius element (in the extension `N/K`) at some prime `P` of
`𝓞 N` above `𝔭`. -/
theorem exists_isFrobAt_of_isFrobAtPrime_under {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {𝒬 : NK.Chebotarev.PrimeIdeal ↥M}
    (hQ : 𝒬.asIdeal.LiesOver 𝔭.asIdeal)
    (hf : 𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1)
    {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩)) :
    ∃ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ := by
  obtain ⟨P, hPQ, hPτ⟩ := hfrob
  refine ⟨P, ?_, ?_⟩
  · -- `P` lies over `𝒬` which lies over `𝔭`
    haveI := hPQ
    haveI := hQ
    exact Ideal.LiesOver.trans P.asIdeal 𝒬.asIdeal 𝔭.asIdeal
  · -- the congruence defining the Frobenius of `N/K` at `P`
    rw [NK.Chebotarev.isFrobAt_def] at hPτ ⊢
    intro x
    have hsub : P.asIdeal.under (NumberField.RingOfIntegers ↥M) = 𝒬.asIdeal := hPQ.over.symm
    rw [hsub] at hPτ
    -- `σ` and the image `τ` of `σ` in `Gal(N/M)` induce the same map on `𝓞 N`
    have h1 : galRestrict (NumberField.RingOfIntegers K) K N (NumberField.RingOfIntegers N) σ x
        = galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N)
            (M.fixingSubgroupEquiv ⟨σ, hσ⟩) x := by
      apply IsFractionRing.injective (NumberField.RingOfIntegers N) N
      rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
      rfl
    -- the residue cardinalities agree because the residue degree of `𝒬` over `𝔭` is one
    have h2 : Nat.card (NumberField.RingOfIntegers ↥M ⧸ 𝒬.asIdeal)
        = Nat.card (NumberField.RingOfIntegers K ⧸ P.asIdeal.under (NumberField.RingOfIntegers K)) := by
      have hsub' : P.asIdeal.under (NumberField.RingOfIntegers K) = 𝔭.asIdeal := by
        rw [← Ideal.under_under (A := NumberField.RingOfIntegers K)
              (B := NumberField.RingOfIntegers ↥M) (C := NumberField.RingOfIntegers N) P.asIdeal,
            hsub, hQ.over]
      rw [hsub']
      haveI := hQ
      have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver (S := NumberField.RingOfIntegers K)
        (R := NumberField.RingOfIntegers ↥M) (P := 𝒬.asIdeal) (p := 𝔭.asIdeal) 𝔭.isPrime 𝔭.ne_bot
      rw [hf, pow_one] at h
      simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using h
    rw [h1, ← h2]
    exact hPτ x

end NK.ChebotarevGeneral
