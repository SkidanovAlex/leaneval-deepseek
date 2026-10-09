import Mathlib
import Submission.Work.SSGRoute.PT.exists_localField_place_data
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat
import Submission.Work.SSGRoute.PT.e1a_beta_can

/-!
# The local place data of the E1a comparison square, hypotheses discharged

`Work.SSGRoute.PT.exists_localField_place_data` bundles the local data of a finite place `A` of `Ω`
(the local field `k_v`, the local closure `Ω_v`, the local level `K' ≅ K_w`, the glue `Φ`, the
coefficient isomorphism `hiso`, and the two pointwise compatibility clauses `hpt`, `hcompatΦ`,
`hψ`), but it takes the primeness data `hLies` and `hAq'` and the `k`-compatibility `hcompat` as
hypotheses.  This module discharges all three from the lying-over condition `hAq` of the E1a node
using `Work.SSGRoute.exists_adicCompletion_algebra_compat` (`hLies` plus the `k`-compatibility) and
`Submission.NeukirchUchida.primeOf_spec` (`hAq'`).

The result is the single input that the per-place comparison square
(`Work.SSGRoute.E1aClean.comparisonSquareFin`) consumes.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

/-- **The local place data at a finite place `A` of `Ω` over the prime `q` of `K`, with every
hypothesis discharged from `hAq`.**  The conclusion is verbatim that of
`Work.SSGRoute.PT.exists_localField_place_data`. -/
theorem exists_localData (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA)
        (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q
        (Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq).choose).toAlgebra
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
  classical
  obtain ⟨hLies, hcompat', -⟩ := Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq
  refine Work.SSGRoute.PT.exists_localField_place_data p k Ω K A hA q hAq hLies
    (Submission.NeukirchUchida.primeOf_spec A hA) ?_
  intro x
  exact (hcompat' x).symm

end Work.SSGRoute.E1aClean
