import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LiftImports
import Submission.Work.SSGRoute.exists_adicCompletion_algebra_compat

namespace Work.SSGRoute

/-- **The two ways of completing agree.**  Let `𝔭` be the prime of `k` below the finite place `A`
of `Ω` (`primeUnder k A hA`), `q` a prime of `K` with `A` above `q` (the compatibility `hAq'`
identifies the trace of `A` with the valuation ring of `q`) and `q` lying over `𝔭`.  Then the
`𝔭`-adic completion of `k` maps to the completion of `Ω` at `A` in the same way whether it passes
through the `q`-adic completion of `K` or not:

```
𝔭.adicCompletion k --adicCompletionMapAt--> q.adicCompletion K --adicCompletionToPlaceCompletion--> Ω_A
                                          =
𝔭.adicCompletion k --------------------adicCompletionToPlaceCompletion-----------------------> Ω_A
```

Both sides are continuous ring homomorphisms out of the completion `𝔭.adicCompletion k`, whose
`k`-image is dense; they agree there because both send `x : k` to `placeCompletionCoe A` of the
image of `x` in `Ω` (the scalar-tower identities `𝒪_k → 𝒪_K → Ω`). -/
theorem adicCompletionToPlaceCompletion_comp (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] [IsSepClosure ↥K Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hAq' : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal) :
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := ↥K) (K' := Ω) q A hAq').comp
        (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies) =
      NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA) := by
  -- The image of `k` in `𝔭.adicCompletion k` is dense.
  have hdense : DenseRange (⇑(algebraMap k ((primeUnder k A hA).adicCompletion k))) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap k (primeUnder k A hA)
  -- Both sides are continuous.
  have hcont1 : Continuous (⇑((NK.NeukirchUchida.adicCompletionToPlaceCompletion
      (K := ↥K) (K' := Ω) q A hAq').comp
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies))) :=
    (NK.NeukirchUchida.continuous_adicCompletionToPlaceCompletion q A hAq').comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous (primeUnder k A hA) q hLies)
  have hcont2 : Continuous (⇑(NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))) :=
    NK.NeukirchUchida.continuous_adicCompletionToPlaceCompletion _ A _
  -- They agree on `k`.
  have hpt : ∀ x : k,
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := ↥K) (K' := Ω) q A hAq')
        ((Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies)
          (algebraMap k ((Work.SSGRoute.primeUnder k A hA).adicCompletion k) x)) =
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))
        (algebraMap k ((Work.SSGRoute.primeUnder k A hA).adicCompletion k) x) := by
    intro x
    -- `algebraMap k (𝔭.adicCompletion k)` is the coercion `k → 𝔭.adicCompletion k`.
    have h1 : algebraMap k ((primeUnder k A hA).adicCompletion k) x =
        { toCompletion := ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation k
          (primeUnder k A hA))).symm x) } := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    -- Same statement one level up, for `K`.
    have h2 : (algebraMap k ↥K x : q.adicCompletion ↥K) =
        algebraMap ↥K (q.adicCompletion ↥K) (algebraMap k ↥K x) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (K := ↥K) (v := q)]
      rfl
    -- `Commons`' completion map at `(𝔭, q)` sends `x` to `algebraMap k ↥K x`.
    have h3 : (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies)
          (algebraMap k ((primeUnder k A hA).adicCompletion k) x) =
        algebraMap ↥K (q.adicCompletion ↥K) (algebraMap k ↥K x) := by
      rw [h1]
      rw [Work.SSGRoute.adicCompletionMapAt]
      rw [Commons.RingTheory.Henselian.adicCompletionMap_apply]
      exact h2
    rw [h3]
    -- Both `adicCompletionToPlaceCompletion`'s are given on `k`/`K` by `placeCompletionCoe`.
    rw [NK.NeukirchUchida.adicCompletionToPlaceCompletion_algebraMap]
    rw [NK.NeukirchUchida.adicCompletionToPlaceCompletion_algebraMap]
    rw [IsScalarTower.algebraMap_apply k ↥K Ω]
  refine DFunLike.coe_injective (DenseRange.equalizer hdense hcont1 hcont2 ?_)
  funext x
  exact hpt x

end Work.SSGRoute
