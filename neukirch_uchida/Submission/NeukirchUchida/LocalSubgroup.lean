import Submission.NeukirchUchida.PlaceSystem
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois

/-!
# The "only if" half of CoNF XII (12.1.9)

The characterisation (12.1.9) of the decomposition groups among the closed subgroups of `G_K` states
that a closed subgroup is a decomposition group if and only if it is self-normalising and isomorphic
to the absolute Galois group of a p-adic field.  This file assembles the *"only if"* half from what
is available:

* non-triviality — `decompositionGroup_ne_bot` (`PlaceSystem.lean`);
* self-normalising — `normalizer_decompositionGroup` (rigidity of places, CoNF (12.1.4));
* isomorphic to `Gal(κ̄/κ)` for `κ = K_𝔭` — the local/global bridge
  `NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`, whose proof identifies
  the decomposition group with the inverse limit of the finite-level local Galois groups and uses
  the cofinality of the completions (`exists_galois_adicCompletion_of_finiteDimensional` in the
  commons, plus its `K'`-side transport
  `NK.NeukirchUchida.exists_finiteGalois_completion_restrict_algEquiv`).
-/

namespace Submission.NeukirchUchida

open scoped Pointwise

/-- **The "only if" half of CoNF XII (12.1.9).**  The decomposition group of a place of the
separable closure over a finite prime of a number field is non-trivial, self-normalising, and
isomorphic to the absolute Galois group of the p-adic completion. -/
theorem isLocalGalois_decompositionGroup {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    decompositionGroup (K₁ := K) (K₁' := K') A ≠ ⊥ ∧
      Subgroup.normalizer (decompositionGroup (K₁ := K) (K₁' := K') A) =
        decompositionGroup (K₁ := K) (K₁' := K') A ∧
      Nonempty (decompositionGroup (K₁ := K) (K₁' := K') A ≃*
        Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) /
          IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) := by
  refine ⟨decompositionGroup_ne_bot ?_, normalizer_decompositionGroup p A hA, ?_⟩
  · rw [hA]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p
  · exact NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois p A hA

end Submission.NeukirchUchida
