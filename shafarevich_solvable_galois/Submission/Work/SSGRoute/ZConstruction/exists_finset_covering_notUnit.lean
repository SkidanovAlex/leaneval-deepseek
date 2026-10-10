import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite cover of the places at which a unit of `↥K` is not a unit

Let `Ω` be an algebraic closure of the number field `k`, `K` a finite Galois intermediate field,
and `X ∈ (↥K)ˣ`.  A finite place `B` of `Ω` may or may not be a *unit* place for `X`, i.e. the
value `B.valuation (algebraMap ↥K Ω X)` may or may not be `1`.  The places where `X` is not a unit
form a union of `K`-conjugacy classes, and this file proves that *finitely many* of them suffice:
there is a finite set `T` of pairwise non-`K`-conjugate finite places of `Ω` such that every finite
place at which `X` is not a unit is `K`-conjugate to an element of `T`.

The mathematical content is the classical finiteness of the set of primes of the number field `↥K`
dividing the principal fractional ideal `(X)`: the `𝔭`-adic valuation of `X` is `1` exactly when
`X` is a `𝔭`-adic unit (`Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero`),
and the support of `𝔭 ↦ count 𝔭 (X)` is finite (`FractionalIdeal.finite_factors`).  For each
remaining prime `𝔭` we pick one finite place of `Ω` above it
(`Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime`, together with the
fact that the restriction to `k` of the valuation ring at `𝔭` is proper), and any two places over
the same prime of `↥K` are conjugate under `Gal(Ω/↥K)`
(`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedVariables false

/-- **`K`-conjugacy preserves the trace on `K`.**  If `B = τ • A` with `τ` fixing `K` pointwise,
then `A` and `B` have the same `K`-prime. -/
theorem comap_eq_of_gesKConj {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) :
    A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
  obtain ⟨τ, hτ, hτA⟩ := h
  have hfix : ∀ y : ↥K, τ⁻¹ • (algebraMap ↥K Ω y) = algebraMap ↥K Ω y := by
    intro y
    rw [AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff K τ⁻¹).mp
      (K.fixingSubgroup.inv_mem hτ) _ y.2
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
  constructor
  · intro hx
    rw [← hτA, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hfix x]
    exact hx
  · intro hx
    rw [← hτA, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hfix x] at hx
    exact hx

/-- **The restriction to `k` of the valuation ring of a prime of `K` is proper.**  For a finite
extension of number fields `k ⊆ K` and a height-one prime `𝔭` of `𝓞 K`, the valuation ring
`𝒪_{K,𝔭}` does *not* contain the image of `k`: the contraction `𝔭 ∩ 𝓞 k` is a nonzero prime of
`𝓞 k` (`Ideal.under_ne_bot`), and the restriction of `𝒪_{K,𝔭}` to `k` is the valuation ring at
that prime (`Commons.RingTheory.Valuation.comap_valuationSubringAtPrime`). -/
theorem comap_valuationSubringAtPrime_ne_top {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭).comap (algebraMap k K) ≠ ⊤ := by
  have hle : 𝔭.asIdeal.LiesOver (𝔭.asIdeal.under (NumberField.RingOfIntegers k)) := inferInstance
  have hprime : (𝔭.asIdeal.under (NumberField.RingOfIntegers k)).IsPrime :=
    Ideal.isPrime_of_liesOver 𝔭.asIdeal (𝔭.asIdeal.under (NumberField.RingOfIntegers k))
  have hne : 𝔭.asIdeal.under (NumberField.RingOfIntegers k) ≠ ⊥ :=
    Ideal.under_ne_bot (NumberField.RingOfIntegers k) 𝔭.ne_bot
  rw [Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
    (⟨𝔭.asIdeal.under (NumberField.RingOfIntegers k), hprime, hne⟩) 𝔭 hle]
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _

/-- **A finite place of `Ω` above a prime of `K`.**  Every height-one prime `𝔭` of `𝓞 ↥K` has an
extension to a valuation subring of `Ω` (Chevalley's extension theorem,
`Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime`), and because the
restriction of `𝒪_{K,𝔭}` to `k` is proper (`comap_valuationSubringAtPrime_ne_top`) the resulting
place of `Ω` is a *finite* place over `k`. -/
theorem exists_isFinPlace_comap_valuationSubringAtPrime {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      A.comap (algebraMap ↥K Ω)
        = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
  obtain ⟨A, hA⟩ := Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
    (K := ↥K) (K' := Ω) 𝔭
  refine ⟨A, ?_, hA⟩
  have key : A.comap (algebraMap k Ω) =
      (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) := by
    rw [ValuationSubring.comap_comap A (algebraMap ↥K Ω) (algebraMap k ↥K),
      ← IsScalarTower.algebraMap_eq k ↥K Ω]
  rw [SSGRoute.IsFinPlace, key, hA]
  exact comap_valuationSubringAtPrime_ne_top 𝔭

/-- **A finite cover of the places at which `X ∈ (↥K)ˣ` is not a unit.**

There is a finite set `T` of finite places of `Ω`, pairwise non-`K`-conjugate, such that every
finite place `B` of `Ω` with `B.valuation (algebraMap ↥K Ω X) ≠ 1` is `K`-conjugate to an element
of `T`.

Take the (finite) set `S` of primes `𝔭` of `𝓞 ↥K` at which `X` is not a `𝔭`-adic unit, and one
finite place `A 𝔭` of `Ω` above each of them.  For a place `B` at which `X` is not a unit, the
prime `𝔭` of `𝓞 ↥K` below `B` lies in `S` (by
`Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero`), so `B` and `A 𝔭` have the
same trace on `↥K` and are conjugate by `Gal(Ω/↥K)`
(`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois`).  Pairwise non-conjugacy is
`comap_eq_of_gesKConj` plus injectivity of `𝔭 ↦ 𝒪_{K,𝔭}`. -/
theorem exists_finset_covering_notUnit {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (X : (↥K)ˣ) :
    ∃ T : Finset (ValuationSubring Ω), (∀ A ∈ T, _root_.SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B) ∧
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        B.valuation (algebraMap ↥K Ω (X : ↥K)) ≠ 1 → ∃ A ∈ T, Work.SSGRoute.gesKConj K A B) := by
  classical
  -- ## 1. the finite set of primes of `𝓞 ↥K` at which `X` is not a unit
  let 𝓘 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (X : ↥K)
  have hfin : {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) |
      FractionalIdeal.count ↥K 𝔭 𝓘 ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥K) 𝓘)
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :=
    hfin.toFinset
  have hS : ∀ 𝔭, 𝔭 ∈ S ↔ FractionalIdeal.count ↥K 𝔭 𝓘 ≠ 0 := fun 𝔭 => hfin.mem_toFinset
  -- ## 2. a chosen finite place of `Ω` above each of these primes
  let A : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) →
      ValuationSubring Ω := fun 𝔭 => (exists_isFinPlace_comap_valuationSubringAtPrime 𝔭).choose
  have hAfin : ∀ 𝔭, SSGRoute.IsFinPlace k (A 𝔭) :=
    fun 𝔭 => (exists_isFinPlace_comap_valuationSubringAtPrime 𝔭).choose_spec.1
  have hAcomap : ∀ 𝔭, (A 𝔭).comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    fun 𝔭 => (exists_isFinPlace_comap_valuationSubringAtPrime 𝔭).choose_spec.2
  refine ⟨S.image A, ?_, ?_, ?_⟩
  · -- ## 3. finiteness of the places of `T`
    intro B hB
    obtain ⟨𝔭, -, rfl⟩ := Finset.mem_image.mp hB
    exact hAfin 𝔭
  · -- ## 4. pairwise non-`K`-conjugacy
    intro B hB C hC hBC
    obtain ⟨𝔭, -, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨𝔮, -, rfl⟩ := Finset.mem_image.mp hC
    have hc : (A 𝔭).comap (algebraMap ↥K Ω) = (A 𝔮).comap (algebraMap ↥K Ω) :=
      comap_eq_of_gesKConj hBC
    rw [hAcomap 𝔭, hAcomap 𝔮] at hc
    have hpq : 𝔭 = 𝔮 := Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hc
    rw [hpq]
  · -- ## 5. the cover clause
    intro B hB hBX
    obtain ⟨𝔭, h𝔭⟩ := Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K B hB
    -- `𝔭` is one of the primes at which `X` is not a unit
    have hcount : FractionalIdeal.count ↥K 𝔭 𝓘 ≠ 0 := fun h0 =>
      hBX ((Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero B 𝔭 h𝔭 X).mpr h0)
    refine ⟨A 𝔭, Finset.mem_image_of_mem _ ((hS 𝔭).mpr hcount), ?_⟩
    -- `B` and `A 𝔭` have the same trace on `↥K`, hence are `Gal(Ω/↥K)`-conjugate
    have htop : (A 𝔭).comap (algebraMap ↥K Ω) ≠ ⊤ := by
      rw [hAcomap 𝔭]
      exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
    have heq : (A 𝔭).comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
      rw [hAcomap 𝔭, h𝔭]
    obtain ⟨σ, hσ⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois
      (F := ↥K) (E := Ω) (A 𝔭) B heq htop
    -- transport `σ : Gal(Ω/↥K)` back to an element of `K.fixingSubgroup ⊆ Gal(Ω/k)`
    refine ⟨((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω), ?_, ?_⟩
    · exact ((IntermediateField.fixingSubgroupEquiv K).symm σ).2
    · rw [← Work.SSGRoute.GrunwaldEscapeCore.gesSmulEqOfCoeEq K (φ := σ)
        (ψ := ((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω)) rfl (A 𝔭)]
      exact hσ

end Work.SSGRoute.ZConstruction
