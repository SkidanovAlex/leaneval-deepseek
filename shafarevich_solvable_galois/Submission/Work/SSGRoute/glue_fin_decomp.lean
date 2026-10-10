import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_finite
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite place of a finite Galois level below a finite place of `Ω`

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K ⊆ Ω` a finite Galois extension of
`k` and `A` a finite place of `Ω` (a nontrivial valuation subring of `Ω` whose trace on `k` is
proper, `SSGRoute.IsFinPlace k A`).

The trace `A ∩ K` is a nontrivial valuation subring of `K` containing `𝓞 K`, hence is the
valuation ring `𝒪_{K,q}` of a unique finite place `q` of `K`.  This `q` is the place of `K` lying
below `A`, and the present lemma records that the decomposition group of `A` restricts *into* the
decomposition group (stabiliser) of `q`:

`(SSGRoute.decomp k A).map (SSGRoute.res k K) ≤ MulAction.stabilizer Gal(K/k) (Place.ofFinite q)`.

The proof is purely local: if `σ` stabilises `A`, then the trace on `K` of `σ • A = A` is the
image of the trace of `A` under the restriction `σ|_K`, so `σ|_K` stabilises the valuation ring
`𝒪_{K,q}`; the Galois action on primes is compatible with the action on valuation rings, so
`σ|_K • q = q`.
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open scoped Pointwise

theorem glue_fin_decomp (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      (SSGRoute.decomp k A).map (SSGRoute.res k K) ≤
        MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (NK.GlobalCFT.Place.ofFinite q) := by
  -- The trace of `A` on `K` is a proper valuation subring of `K`.
  have hB : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro h
    apply hA
    refine le_antisymm le_top (fun x _ => ?_)
    have h1 : algebraMap k ↥K x ∈ A.comap (algebraMap ↥K Ω) := by
      rw [h]; exact ValuationSubring.mem_top _
    have hx : (algebraMap ↥K Ω) ((algebraMap k ↥K) x) ∈ A := by
      rwa [ValuationSubring.mem_comap] at h1
    rw [ValuationSubring.mem_comap, IsScalarTower.algebraMap_apply k ↥K Ω]
    exact hx
  -- Cut out the finite place `q` of `K` by `A ∩ K`.
  obtain ⟨q, hq⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (A.comap (algebraMap ↥K Ω)) hB
      (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
        (A.comap (algebraMap ↥K Ω)) hB)
  refine ⟨q, ?_⟩
  rintro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨σ, hσ, rfl⟩ := hy
  have hσA : σ • A = A := MulAction.mem_stabilizer_iff.mp hσ
  -- The trace on `K` of `σ • A` is the image of the trace of `A` under the restriction `σ|_K`.
  have hkey :=
    NK.Reconstruct.comap_smul_eq_restrictNormalHom_smul' (F := k) (E := ↥K) (K := Ω) A σ
  rw [hσA] at hkey
  have hresB : SSGRoute.res k K σ • (A.comap (algebraMap ↥K Ω)) = A.comap (algebraMap ↥K Ω) :=
    hkey.symm
  -- Hence `σ|_K` stabilises the valuation ring `𝒪_{K,q}`.
  have hval : SSGRoute.res k K σ •
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q := by
    rw [← hq]
    exact hresB
  -- Therefore `σ|_K • q = q`, i.e. `σ|_K` lies in the stabiliser of `Place.ofFinite q`.
  rw [MulAction.mem_stabilizer_iff]
  rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    (R := NumberField.RingOfIntegers ↥K) (K := ↥K)
  have hsmul :=
    Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      (K := k) (L := ↥K) q (NK.GlobalCFT.Place.smulHeightOneSpectrum (SSGRoute.res k K σ) q)
      (SSGRoute.res k K σ)
      (by
        rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
        have he := congrArg
          (fun e : NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K =>
            Ideal.map (e : NumberField.RingOfIntegers ↥K →+* NumberField.RingOfIntegers ↥K)
              q.asIdeal)
          (NK.GlobalCFT.Galois.ringOfIntegersEquiv_eq_galRestrict (SSGRoute.res k K σ))
        exact he)
  rw [hsmul.symm]
  exact hval

end Work.SSGRoute
