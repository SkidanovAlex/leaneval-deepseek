import Mathlib
import Submission.Work.SSGRoute.GlueSetup
import Submission.Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finite places of `Ω` realising a prescribed stabiliser

`Work.SSGRoute.glue_fin_decomp_ex`: every finite place `q` of a finite Galois extension
`K/k` (with `Ω` an algebraic closure of `k` containing `K`) is the trace of a finite place
`A` of `Ω` whose decomposition group `D_A ≤ G_k` maps *onto* the stabiliser of `q`:

`MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (Place.ofFinite q) ≤ (decomp k A).map (res k K)`.

The proof has three steps.

1. **Existence of the place `A`.**  `Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq`
   extends the valuation ring `O_{K,q}` of `q` to a valuation ring `A` of `Ω`; properness of the
   trace on `k` is inherited from properness on `K` (`K/k` is algebraic).
2. **Translation of the stabilisers.**  The stabiliser of the place `Place.ofFinite q` is the
   stabiliser of the valuation ring `O_{K,q}`: both are described by the `q`-adic valuation, and
   the Galois action preserves the latter
   (`Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq`).
3. **Surjectivity onto the decomposition group.**  Apply
   `Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois`, which
   lifts every element of `Gal(K/k)` stabilising `A ∩ K` to an element of `Gal(Ω/k)` stabilising
   `A`.
-/

open scoped Pointwise
open NumberField IsDedekindDomain

namespace Work.SSGRoute

section Helpers

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **The stabiliser of a finite place is the stabiliser of its valuation ring.**
For a finite Galois extension `K/k` of number fields contained in `Ω`, an element
`σ : Gal(K/k)` fixes the finite place `Place.ofFinite q` if and only if it preserves the
valuation ring `O_{K,q}`.  We only need the "only if" direction. -/
theorem stabilizer_ofFinite_le_stabilizer_valuationSubringAtPrime
    (K : IntermediateField k Ω) [NumberField ↥K] [FiniteDimensional k ↥K] [IsGalois k ↥K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (NK.GlobalCFT.Place.ofFinite q) ≤
      MulAction.stabilizer (↥K ≃ₐ[k] ↥K)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q) := by
  intro σ hσ
  -- `σ` fixes the prime ideal `q`, hence preserves the `q`-adic valuation.
  have hfix : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q = q := by
    have h := hσ
    rw [MulAction.mem_stabilizer_iff] at h
    rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj] at h
    exact h
  have hmap : q.asIdeal =
      Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) q.asIdeal :=
    (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hfix).symm
  have hcompat : ∀ r : NumberField.RingOfIntegers ↥K,
      (σ : ↥K ≃+* ↥K) (algebraMap (NumberField.RingOfIntegers ↥K) ↥K r) =
        algebraMap (NumberField.RingOfIntegers ↥K) ↥K
          (NK.GlobalCFT.Place.ringOfIntegersEquiv σ r) :=
    fun r => (NK.GlobalCFT.Place.ringOfIntegersEquiv_apply σ r).symm
  have hval : ∀ x : ↥K,
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K q (σ x) =
        IsDedekindDomain.HeightOneSpectrum.valuation ↥K q x :=
    fun x => Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
      (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) (σ : ↥K ≃+* ↥K) hcompat q q hmap x
  -- Membership in the valuation ring is the condition `q.valuation x ≤ 1`.
  rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff]
  intro x
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff, hval x]

/-- **Existence of a finite place of `Ω` with a prescribed trace on `K`.**
Every finite place `q` of `K` extends to a valuation ring `A` of `Ω` with
`A ∩ K = O_{K,q}`; since `K/k` is algebraic, `A` is a finite place of `Ω` over `k`. -/
theorem exists_isFinPlace_comap_eq (K : IntermediateField k Ω) [NumberField ↥K]
    [FiniteDimensional k ↥K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    ∃ A : ValuationSubring Ω,
      A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q ∧
        SSGRoute.IsFinPlace k A := by
  classical
  obtain ⟨A, hA⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
    (K := ↥K) (L := Ω) (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q)
  refine ⟨A, hA, ?_⟩
  -- The trace on `k` is the trace of the trace on `K`.
  rw [SSGRoute.IsFinPlace]
  intro htop
  have hcomp : A.comap (algebraMap k Ω) =
      (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) := by
    rw [IsScalarTower.algebraMap_eq k ↥K Ω, ← ValuationSubring.comap_comap]
  rw [hcomp, hA] at htop
  -- If `A` contained `k`, it would contain the algebraic extension `K` of `k`.
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := ↥K) q ?_
  exact Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q)
    (Algebra.IsAlgebraic.of_finite k ↥K) htop

end Helpers

theorem glue_fin_decomp_ex (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (NK.GlobalCFT.Place.ofFinite q) ≤
        (SSGRoute.decomp k A).map (SSGRoute.res k K) := by
  classical
  obtain ⟨A, hAcomap, hAfin⟩ := exists_isFinPlace_comap_eq (k := k) (Ω := Ω) K q
  refine ⟨A, hAfin, ?_⟩
  intro τ hτ
  -- The element `τ` stabilises the trace `A ∩ K = O_{K,q}` of `A` on `K`.
  have hτ' : τ ∈ MulAction.stabilizer (↥K ≃ₐ[k] ↥K) (A.comap (algebraMap ↥K Ω)) := by
    rw [hAcomap]
    exact stabilizer_ofFinite_le_stabilizer_valuationSubringAtPrime K q hτ
  -- Lift it to an element of the decomposition group of `A`.
  obtain ⟨σ, hσ, hres⟩ :=
    Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
      (F := k) (E := Ω) A hAfin K τ hτ'
  exact ⟨σ, hσ, hres⟩

end Work.SSGRoute
