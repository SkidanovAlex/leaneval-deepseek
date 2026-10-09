import Mathlib
import Submission.Work.SSGRoute.localField_subfield_place_compat_coIn
import Submission.Work.SSGRoute.localField_subfield_place_compat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

namespace Work.SSGRoute.PT

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

/-- **The bundled local place data of a finite place `A` of `Ω`, together with the `Ω`-compatibility
of the coefficient embedding.**

This is the conjunction of `Work.SSGRoute.localField_subfield_place_compat` (the local field
`K_w = q.adicCompletion K` with its decomposition-group action, the isomorphism `ψ` onto a finite
Galois subextension `K'` of `localClosureAt k A hA`, the homeomorphism `Φ`, and `eG`) with the
extra clause of `Work.SSGRoute.localField_subfield_place_compat_coIn`: a ring homomorphism `e`
from `adjoinPlaceCompletion` to the local closure realising the embedding of `K` given by the
completion as the embedding given by the place through `Ω`.

Both constructions are the same one (`K' = θ'.fieldRange`, `ψ = θ'.equivFieldRange.symm` for the
`k_v`-algebra map `θ' = e ∘ θM : q.adicCompletion K → localClosureAt` produced by
`exists_algHom_adicCompletion_adjoinPlaceCompletion`), so we run it once and export all clauses. -/
theorem exists_localField_place_data (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal)
    (hAq' : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (Work.SSGRoute.primeUnder k A hA)) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA)
        (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A hAq').toAlgebra
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
    (∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x)) →
    ∃ (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
          (Work.SSGRoute.localClosureAt k A hA))
      (_ : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K')
      (_ : IsGalois (Work.SSGRoute.localFieldAt k A hA) K')
      (ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K))
      (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
      (Φ : ↥(SSGRoute.decomp k A) ≃*
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA))
      (e : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A) →+*
          Work.SSGRoute.localClosureAt k A hA),
      IsHomeomorph (Φ : ↥(SSGRoute.decomp k A) →
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA)) ∧
      Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
        Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
          (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))) ∧
      (∀ (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (y : ↥K'),
        (eG σ) y = ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) σ (ψ y))) ∧
      (∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
        (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
          ψ.symm (algebraMap K (q.adicCompletion K)
            ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x))) ∧
      (∀ y : K, ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
          Work.SSGRoute.localClosureAt k A hA) =
        e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
          (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y))) := by
  intro hcompat
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  -- the `K`-version of the compatibility of the place with the prime, used to build `θM`
  have hAqK := place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A hAq').toAlgebra
  haveI : IsScalarTower k (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq (fun x => hcompat x)
  have hcont : Continuous
      (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)) :=
    Work.LocalFields.completion_algebraMap_continuous (K := k) (L := ↥K)
      (Work.SSGRoute.primeUnder k A hA) q
  haveI : ContinuousSMul (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    continuousSMul_of_algebraMap _ _ hcont
  haveI : Module.Finite (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) := inferInstance
  haveI : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) := inferInstance
  haveI : IsGalois (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    Work.LocalFields.isGalois_completion (K := k) (L := ↥K) (Work.SSGRoute.primeUnder k A hA) q
  have hlin : ∀ c : Work.SSGRoute.localFieldAt k A hA,
      NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := ↥K) (K' := Ω) q A hAqK
          (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) c) =
        algebraMap (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) c :=
    fun c => RingHom.congr_fun
      (adicCompletionToPlaceCompletion_comp k Ω K A hA q hAq hAqK hLies) c
  obtain ⟨θM, hθM⟩ :=
    exists_algHom_adicCompletion_adjoinPlaceCompletion k Ω K A hA q hAq hAqK hLies hlin
  let e := NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
    hAq' (fun z => rfl)
  let θ' : (q.adicCompletion K) →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA) :=
    (show ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A) →ₐ[Work.SSGRoute.localFieldAt k A hA]
        (Work.SSGRoute.localClosureAt k A hA) from e.toAlgHom).comp θM
  let K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) := θ'.fieldRange
  let ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K) :=
    θ'.equivFieldRange.symm
  haveI hfd : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K' :=
    LinearEquiv.finiteDimensional θ'.equivFieldRange.toLinearEquiv
  haveI hgal : IsGalois (Work.SSGRoute.localFieldAt k A hA) K' :=
    IsGalois.of_algEquiv θ'.equivFieldRange
  obtain ⟨eG, hiso, hpt⟩ := localUnitsK_iso_intermediateField_pointwise k Ω K A hA q hLies K' ψ
  let Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) :=
    NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      hAq' (fun z => rfl)
      (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
        (Work.SSGRoute.primeUnder k A hA) A hAq')
  have hΦ : IsHomeomorph (Φ : ↥(SSGRoute.decomp k A) →
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA)) :=
    isHomeomorph_localGaloisEquiv k Ω A hA
  have hψ : ∀ y : K,
      ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
        Work.SSGRoute.localClosureAt k A hA) =
      e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y)) := by
    intro y
    have h1 : ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
        Work.SSGRoute.localClosureAt k A hA) =
        θ' (algebraMap K (q.adicCompletion K) y) :=
      AlgHom.equivFieldRange_apply_coe θ' (algebraMap K (q.adicCompletion K) y)
    rw [h1]
    show e (θM (algebraMap K (q.adicCompletion K) y)) =
      e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y))
    rw [hθM y]
  have h4 : ∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
      (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
        ψ.symm (algebraMap K (q.adicCompletion K)
          ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)) := by
    intro σ x
    rw [hψ x, hψ ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)]
    exact localGaloisEquiv_adjoin_coInAdjoin_compat k Ω K A hA σ x
  exact ⟨K', hfd, hgal, ψ, eG, Φ,
    (e.toRingEquiv : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A) →+* Work.SSGRoute.localClosureAt k A hA),
    hΦ, hiso, hpt, h4, hψ⟩

end Work.SSGRoute.PT
