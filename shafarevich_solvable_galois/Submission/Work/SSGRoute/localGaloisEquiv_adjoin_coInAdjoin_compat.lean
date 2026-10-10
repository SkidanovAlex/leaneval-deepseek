import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.Work.SSGRoute.E7aAux

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- Conjugation of an automorphism by an algebra equivalence, evaluated at the image of a point:
`(autCongr e f) (e y) = e (f y)`. -/
lemma algEquiv_autCongr_apply_apply {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (f : A ≃ₐ[R] A) (y : A) :
    (AlgEquiv.autCongr e f) (e y) = e (f y) := by
  simp [AlgEquiv.autCongr_apply]

/-- The compatibility of `NK.Mine.localGaloisEquiv` with `NK.Mine.adjoinSepEquiv` in the general
form in which it is proved: the prime `p` of `k` below `A` and the side conditions `halg` and
`hW` are explicit hypotheses rather than the `Work.SSGRoute` abbreviations. -/
theorem localGaloisEquiv_adjoinSepEquiv_coInAdjoin (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [IsGalois k K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    (hA : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k p)
      (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion k p,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z)
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k p)
    (σ : ↥(SSGRoute.decomp k A)) (x : K) :
    (NK.Mine.localGaloisEquiv (K := k) (K' := Ω) p A hA halg hW σ)
        (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A (algebraMap K Ω x))) =
      NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A
          (algebraMap K Ω (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) x))) := by
  have hstep : (σ : Ω ≃ₐ[k] Ω) (algebraMap K Ω x)
      = algebraMap K Ω (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) x) :=
    (AlgEquiv.restrictNormalHom_apply K (σ : Ω ≃ₐ[k] Ω) x).symm
  have hloc : (NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) p A hA halg hW σ)
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A (algebraMap K Ω x))
      = NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A
          ((σ : Ω ≃ₐ[k] Ω) (algebraMap K Ω x)) :=
    (DFunLike.congr_fun
        (NK.Mine.adjoinLocalEquiv_apply (K := k) (K' := Ω) p A hA halg hW σ)
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A (algebraMap K Ω x))).trans
      (NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := k) (K' := Ω) p A hA halg σ
        (algebraMap K Ω x))
  calc
    (NK.Mine.localGaloisEquiv (K := k) (K' := Ω) p A hA halg hW σ)
        (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A (algebraMap K Ω x)))
      = AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg)
          (NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) p A hA halg hW σ)
          (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
            (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A (algebraMap K Ω x))) := rfl
    _ = NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
          ((NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) p A hA halg hW σ)
            (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A (algebraMap K Ω x))) :=
        algEquiv_autCongr_apply_apply _ _ _
    _ = NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A
            ((σ : Ω ≃ₐ[k] Ω) (algebraMap K Ω x))) :=
        congrArg (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg) hloc
    _ = NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A
            (algebraMap K Ω (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) x))) :=
        congrArg (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) p A hA halg)
          (congrArg (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) p A) hstep)

theorem localGaloisEquiv_adjoin_coInAdjoin_compat (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
    ∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
      (NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
            (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)) σ)
        (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
          (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
            (algebraMap K Ω x))) =
      NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
        (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
          (algebraMap K Ω (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) x))) := by
  intro σ x
  letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k
      (Work.SSGRoute.primeUnder k A hA)) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  exact localGaloisEquiv_adjoinSepEquiv_coInAdjoin (k := k) (Ω := Ω) (K := K)
    (p := Work.SSGRoute.primeUnder k A hA) (A := A)
    (hA := Submission.NeukirchUchida.primeOf_spec A hA)
    (halg := fun z => rfl)
    (hW := NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))
    σ x

end

end Work.SSGRoute
