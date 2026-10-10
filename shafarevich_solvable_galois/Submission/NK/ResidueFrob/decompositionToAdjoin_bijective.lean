import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_adjoin

namespace NK.ResidueFrob

open NK.NeukirchUchida

theorem decompositionToAdjoin_bijective {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p) :
    Function.Bijective (NK.NeukirchUchida.decompositionToAdjoin p A hA halg) := by
  constructor
  · intro σ τ h
    refine Subtype.ext (AlgEquiv.ext fun y => ?_)
    apply RingHom.injective (placeCompletionCoe A)
    have h' := congrArg
      (fun φ : adjoinPlaceCompletion (K := K) (K' := K') p A ≃ₐ[
          IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
          adjoinPlaceCompletion (K := K) (K' := K') p A =>
        ((φ (coInAdjoin (K := K) (K' := K') p A y) :
          adjoinPlaceCompletion (K := K) (K' := K') p A) : placeCompletion A)) h
    rw [decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg σ y,
      decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg τ y] at h'
    simpa only [coe_coInAdjoin] using h'
  · intro τ
    obtain ⟨σ, hσ⟩ := exists_mem_decompositionGroupOf_of_algEquiv_adjoin (K := K) (K' := K')
      p A hA halg hW τ
    refine ⟨σ, ?_⟩
    refine algEquiv_ext_adjoin (K := K) (K' := K') p A hA halg _ _ fun y => ?_
    refine Subtype.ext ?_
    show ((decompositionToAdjoin (K := K) (K' := K') p A hA halg σ)
        (coInAdjoin (K := K) (K' := K') p A y) : placeCompletion A) =
      ((τ (coInAdjoin (K := K) (K' := K') p A y) :
        adjoinPlaceCompletion (K := K) (K' := K') p A) : placeCompletion A)
    rw [decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg σ y]
    exact (hσ y).symm

end NK.ResidueFrob
