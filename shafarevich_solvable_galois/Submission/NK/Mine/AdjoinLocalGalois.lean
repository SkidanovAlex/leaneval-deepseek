import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.ResidueFrob.decompositionToAdjoin_bijective
import Submission.NK.ResidueFrob.isSepClosure_adjoinPlaceCompletion

namespace NK.Mine

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The restriction of the extension of `σ ∈ D_A` to `M = κ·K'`**, as a monoid homomorphism.
Its underlying function is `NK.NeukirchUchida.decompositionToAdjoin`. -/
noncomputable def adjoinLocalHom
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z) :
    NK.Mine.decompositionGroupOf K K' A →*
      (NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A ≃ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
        NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) where
  toFun σ := NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ
  map_one' := by
    refine NK.NeukirchUchida.algEquiv_ext_adjoin (K := K) (K' := K') p A hA halg _ _ fun y => ?_
    rw [NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg 1 y]
    rfl
  map_mul' σ τ := by
    refine NK.NeukirchUchida.algEquiv_ext_adjoin (K := K) (K' := K') p A hA halg _ _ fun y => ?_
    rw [AlgEquiv.mul_apply,
      NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg τ y,
      NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg σ (τ.1 y),
      NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := K) (K' := K') p A hA halg (σ * τ) y]
    rfl

@[simp]
theorem adjoinLocalHom_apply
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z)
    (σ : NK.Mine.decompositionGroupOf K K' A) :
    adjoinLocalHom p A hA halg σ =
      NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ := rfl

/-- **The decomposition group of `A` is the group of `κ`-algebra automorphisms of `M = κ·K'`.**

The underlying function of this isomorphism is `NK.NeukirchUchida.decompositionToAdjoin`. -/
noncomputable def adjoinLocalEquiv
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
    NK.Mine.decompositionGroupOf K K' A ≃*
      (NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A ≃ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
        NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :=
  MulEquiv.ofBijective (adjoinLocalHom p A hA halg)
    (NK.ResidueFrob.decompositionToAdjoin_bijective p A hA halg hW)

@[simp]
theorem adjoinLocalEquiv_apply
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
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p)
    (σ : NK.Mine.decompositionGroupOf K K' A) :
    adjoinLocalEquiv p A hA halg hW σ =
      NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ := rfl

/-- **`M = κ·K'` is a separable closure of `κ`.** -/
theorem isSepClosure_adjoinPlaceCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z) :
    IsSepClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :=
  NK.ResidueFrob.isSepClosure_adjoinPlaceCompletion p A hA halg

/-- **The isomorphism of separable closures `M ≃ₐ[κ] κ^sep`** used to identify `Aut_κ(M)` with
`Gal(κ^sep/κ)`. -/
noncomputable def adjoinSepEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z) :
    ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
      SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) := by
  haveI : IsSepClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A) :=
    NK.ResidueFrob.isSepClosure_adjoinPlaceCompletion p A hA halg
  exact IsSepClosure.equiv (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
    ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := K) (K' := K') p A)
    (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p))

/-- **The decomposition group of `A` is the absolute Galois group of the completion `κ = K_𝔭`**:
the composite of `adjoinLocalEquiv` with the conjugation isomorphism induced by an isomorphism
`M ≃ₐ[κ] κ^sep` of separable closures. -/
noncomputable def localGaloisEquiv
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
    NK.Mine.decompositionGroupOf K K' A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) :=
  (adjoinLocalEquiv p A hA halg hW).trans (AlgEquiv.autCongr (adjoinSepEquiv p A hA halg))

end

end NK.Mine
