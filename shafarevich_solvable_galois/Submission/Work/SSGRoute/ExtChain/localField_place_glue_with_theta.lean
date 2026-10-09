import Mathlib
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.ExtChain.adicCompletion_eq_adjoin_image
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs

/-!
# The E7a place glue, exported together with the embedding `θ'`

`Work.SSGRoute.localField_subfield_place_compat` produces the local data of the place `A` of `Ω`
in the form `(K', ψ, eG, Φ)`, with `K'` an intermediate field of the local closure.  Downstream
(the E1a chain comparison) one rather needs the *embedding* `θ' : K_w → localClosureAt` of which
`ψ` is the inverse: the clause `θ' (algebraMap K K_w y) = ψ.symm (algebraMap K K_w y)` and the
statement that `θ'` is the canonical embedding of the completion, i.e. that the image of `K`
generates its range over `k_v`.

This file states and proves exactly that variant of the glue, adding to the four clauses of
`localField_subfield_place_compat` the two clauses about `θ'`.
-/

namespace Work.SSGRoute.ExtChain

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000

/-- **Generation is transported by an `F`-algebra isomorphism.**  If the image of `g : ι → A`
generates `A` over `F`, then the image of `g` under `e.symm` generates `↥K'` over `F`, for any
`F`-algebra isomorphism `e : ↥K' ≃ₐ[F] A`.

Note the ambient field of the conclusion is `↥K'` (the elements `e.symm (g i)` live in `K'`). -/
theorem adjoin_range_algEquiv_symm_eq_top {F A B : Type*} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B] (K' : IntermediateField F B) (e : ↥K' ≃ₐ[F] A)
    {ι : Type*} (g : ι → A)
    (h : IntermediateField.adjoin F (Set.range g) = ⊤) :
    (IntermediateField.adjoin F (Set.range (fun i => e.symm (g i))) :
      IntermediateField F ↥K') = ⊤ := by
  have hmap : (IntermediateField.adjoin F (Set.range g)).map e.symm.toAlgHom ≤
      IntermediateField.adjoin F (Set.range (fun i => e.symm (g i))) := by
    rw [IntermediateField.map_le_iff_le_comap, IntermediateField.adjoin_le_iff]
    rintro a ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  have htop : (⊤ : IntermediateField F A).map e.symm.toAlgHom = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [IntermediateField.mem_map]
    exact ⟨e y, trivial, by simp⟩
  rw [h, htop] at hmap
  exact top_le_iff.mp hmap

/-- **E7a place glue, with the embedding `θ'` made explicit.**

This is `Work.SSGRoute.localField_subfield_place_compat` with the existential unpacked one step
further: besides the four clauses about `(K', ψ, eG, Φ)` it exports the `k_v`-algebra embedding
`θ' : K_w → localClosureAt` with `ψ = θ'.equivFieldRange.symm`, the agreement
`θ' (algebraMap K K_w y) = ψ.symm (algebraMap K K_w y)`, and the fact that `θ'`'s range is
generated over `k_v` by the image of `K`. -/
theorem localField_place_glue_with_theta (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
    ∃ (θ' : q.adicCompletion K →ₐ[Work.SSGRoute.localFieldAt k A hA]
          (Work.SSGRoute.localClosureAt k A hA))
      (_ : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) θ'.fieldRange)
      (_ : IsGalois (Work.SSGRoute.localFieldAt k A hA) θ'.fieldRange)
      (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (θ'.fieldRange ≃ₐ[Work.SSGRoute.localFieldAt k A hA] θ'.fieldRange))
      (Φ : ↥(SSGRoute.decomp k A) ≃*
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA)),
      (let K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
            (Work.SSGRoute.localClosureAt k A hA) := θ'.fieldRange
       let ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K) :=
         θ'.equivFieldRange.symm
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
           Work.SSGRoute.localClosureAt k A hA) = θ' (algebraMap K (q.adicCompletion K) y)) ∧
       (IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
         (Set.range (fun x : K => ψ.symm (algebraMap K (q.adicCompletion K) x))) = ⊤)) := by
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
  obtain ⟨θM, hθM⟩ :=
    exists_algHom_adicCompletion_adjoinPlaceCompletion k Ω K A hA q hAq hAq' hLies hlin
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
  have hθ : ∀ y : K, ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
      Work.SSGRoute.localClosureAt k A hA) = θ' (algebraMap K (q.adicCompletion K) y) :=
    fun y => AlgHom.equivFieldRange_apply_coe θ' (algebraMap K (q.adicCompletion K) y)
  have h4 : ∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
      (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
        ψ.symm (algebraMap K (q.adicCompletion K)
          ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)) := by
    intro σ x
    rw [hψ x, hψ ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)]
    exact localGaloisEquiv_adjoin_coInAdjoin_compat k Ω K A hA σ x
  have hadj : (IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
      (Set.range (fun x : K => ψ.symm (algebraMap K (q.adicCompletion K) x))) :
        IntermediateField (Work.SSGRoute.localFieldAt k A hA) ↥K') = ⊤ :=
    adjoin_range_algEquiv_symm_eq_top (F := Work.SSGRoute.localFieldAt k A hA)
      (A := q.adicCompletion K) (B := Work.SSGRoute.localClosureAt k A hA) K' ψ
      (fun x : K => algebraMap K (q.adicCompletion K) x)
      (adicCompletion_eq_adjoin_image p k Ω K A hA q hAq hLies hcompat)
  exact ⟨θ', hfd, hgal, eG, Φ, hΦ, hiso, hpt, h4, hθ, hadj⟩

end Work.SSGRoute.ExtChain
