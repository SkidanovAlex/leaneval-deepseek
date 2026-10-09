import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.localUnitsK_iso_intermediateField
import Submission.Work.SSGRoute.exists_localField_subfield
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat
import Submission.Work.SSGRoute.localAutHom_bijective
import Submission.Work.SSGRoute.LiftImports
import Submission.Work.SSGRoute.place_comap_valuationSubringAtPrime
import Submission.Work.SSGRoute.adicCompletionToPlaceCompletion_comp
import Submission.Work.SSGRoute.exists_algHom_adicCompletion_adjoinPlaceCompletion
import Submission.Work.SSGRoute.localUnitsK_iso_intermediateField_pointwise
import Submission.Work.SSGRoute.localGaloisEquiv_adjoin_coInAdjoin_compat
import Submission.Work.SSGRoute.isHomeomorph_localGaloisEquiv
set_option synthInstance.maxHeartbeats 400000

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

/-- **E7a place glue, completed** (the statement of `localField_subfield_place_glue`).

The proof assembles the pieces: the prime of `K` below `A`
(`Work.SSGRoute.place_comap_valuationSubringAtPrime`), the `k_v`-linearity of
`C = placeCompletion A` over `K_w = q.adicCompletion K`
(`Work.SSGRoute.adicCompletionToPlaceCompletion_comp`), the `k_v`-algebra map
`K_w -> M = k_v.Omega` carrying `K` to the image of `K`
(`Work.SSGRoute.exists_algHom_adicCompletion_adjoinPlaceCompletion`), the induced
algebra isomorphism `psi : K' = theta''.fieldRange ~= K_w`, `Phi = NK.Mine.localGaloisEquiv`
(a homeomorphism, whose action on the image of `K` in `M` is `sigma`:
`Work.SSGRoute.localGaloisEquiv_adjoin_coInAdjoin_compat`), and `eG` with the pointwise
description of the local action (`Work.SSGRoute.localUnitsK_iso_intermediateField_pointwise`). -/
theorem localField_subfield_place_compat (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal) :
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
      (eG : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
      (Φ : ↥(SSGRoute.decomp k A) ≃*
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA)),
      IsHomeomorph (Φ : ↥(SSGRoute.decomp k A) →
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA)) ∧
      Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
        Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
          (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))) ∧
      (∀ (σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (y : ↥K'),
        (eG σ) y = ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) σ (ψ y))) ∧
      (∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
        (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
          ψ.symm (algebraMap K (q.adicCompletion K)
            ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x))) := by
  intro hcompat
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  have hAq' := place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
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
      NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := ↥K) (K' := Ω) q A hAq'
          (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) c) =
        algebraMap (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) c :=
    fun c => RingHom.congr_fun
      (adicCompletionToPlaceCompletion_comp k Ω K A hA q hAq hAq' hLies) c
  obtain ⟨θM, hθM⟩ := exists_algHom_adicCompletion_adjoinPlaceCompletion k Ω K A hA q hAq hAq' hLies hlin
  let e := NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
    (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
  let θ' : (q.adicCompletion K) →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA) :=
    e.toAlgHom.comp θM
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
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
      (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))
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
  exact ⟨K', hfd, hgal, ψ, eG, Φ, hΦ, hiso, hpt, h4⟩

end Work.SSGRoute
