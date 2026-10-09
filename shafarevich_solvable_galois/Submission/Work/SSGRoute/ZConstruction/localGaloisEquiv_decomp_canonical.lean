import Mathlib
import Submission.Work.SSGRoute.ZConstruction.localGaloisEquiv_decomp

/-!
# The level-`K` local Galois identification, pinned to the canonical prime

`Work.SSGRoute.ZConstruction.localGaloisEquiv_decomp` identifies the level-`K` local group
`↥(decomp (k := ↥K) A)` with the absolute Galois group of a completion, but only **existentially**
in the prime `𝔭`.  Every consumer, however, uses the *canonical* prime
`𝔭 := Submission.NeukirchUchida.primeOf A hAK` (`hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤`): that is the
prime from which `Work.SSGRoute.PTembedding.localFieldOf ↥K A hAK` and
`…localGalOf ↥K A hAK` are *defined* (so that `PTembedding.lcHoms_localUnits` and
`Work.SSGRoute.adicCompletion_units_mul_pow` match the cardinality statements by `rfl`).

This file pins the witness down.  With it, the local Kummer count at the level-`K` local group is

  `|lcHoms p ↥(decomp (k := ↥K) A)| = |lcHoms p Gal(κ̄/κ)| = |κˣ ⧸ (κˣ)^p|`

by `Work.SSGRoute.ZConstruction.natCard_lcHoms_congr` (transport along a topological group
isomorphism) and `Work.SSGRoute.PTembedding.lcHoms_localUnits` (the local count), where
`κ = 𝔭.adicCompletion ↥K` and `𝔭 = primeOf A hAK` in both occurrences.
-/

namespace Work.SSGRoute.ZConstruction

/-- **The composite identification `decomp (k := ↥K) A ≃* Gal(κ̄/κ)` at the canonical prime
`𝔭 = primeOf A hAK`, as a homeomorphism.** -/
theorem localGaloisEquiv_decomp_canonical
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    ∃ e : ↥(SSGRoute.decomp (k := ↥K) A) ≃*
        (SeparableClosure ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K) ≃ₐ[
          (Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K]
          SeparableClosure ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)),
      IsHomeomorph (e : ↥(SSGRoute.decomp (k := ↥K) A) →
        (SeparableClosure ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K) ≃ₐ[
          (Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K]
          SeparableClosure ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K))) := by
  classical
  -- `Ω` is a separable closure of `↥K` (char. 0)
  haveI : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- the canonical prime of `↥K` below `A`, and the completion `κ = 𝔭.adicCompletion ↥K`
  set 𝔭 := Submission.NeukirchUchida.primeOf A hAK with h𝔭def
  have h𝔭 := Submission.NeukirchUchida.primeOf_spec A hAK
  letI : Algebra (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion ↥K,
      (algebraMap (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭 z := fun z => rfl
  have hW :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A h𝔭
  haveI : IsSepClosure (𝔭.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A h𝔭 halg
  exact ⟨NK.Mine.localGaloisEquiv 𝔭 A h𝔭 halg hW,
    NK.Mine.isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
      (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))⟩

end Work.SSGRoute.ZConstruction
