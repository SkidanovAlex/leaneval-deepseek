import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers

open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

/-- The algebra maps between the `WithVal`-spaces are compatible along a tower of number fields:
this is the defining property of the algebra maps, transported to `WithVal`. -/
lemma withVal_algebraMap_comp {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M)) :
    (algebraMap (WithVal (q.valuation L)) (WithVal (r.valuation M))).comp
      (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L))) =
    (algebraMap (WithVal (Q.valuation K)) (WithVal (r.valuation M))) := by
  ext x
  simp only [RingHom.comp_apply, WithVal.algebraMap_right_apply, WithVal.algebraMap_left_apply]
  rw [IsScalarTower.algebraMap_apply K L M]

/-- The maps induced on the uniform-space completions by the `WithVal`-algebra maps compose. -/
lemma completionMapRingHom_comp {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hr : r.asIdeal.LiesOver q.asIdeal)
    (hQ : r.asIdeal.LiesOver Q.asIdeal) :
    (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (q.valuation L)) (WithVal (r.valuation M)))
        (Commons.RingTheory.Henselian.withValMap_continuous q r hr)).comp
      (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L)))
        (Commons.RingTheory.Henselian.withValMap_continuous Q q hq))
    = UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (Q.valuation K)) (WithVal (r.valuation M)))
        (Commons.RingTheory.Henselian.withValMap_continuous Q r hQ) := by
  rw [UniformSpace.Completion.mapRingHom_comp]
  congr 1
  · exact withVal_algebraMap_comp Q q r

/-- Unfolding of `adicCompletionMap` on a point: it is the inverse of the comparison
isomorphism `L_q ≃ (q.valuation L).Completion` applied to the completion of the algebra map. -/
lemma adicCompletionMap_apply_def {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : Q.adicCompletion K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq x =
      (adicCompletion.equiv L q).symm
        (UniformSpace.Completion.mapRingHom
          (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L)))
          (Commons.RingTheory.Henselian.withValMap_continuous Q q hq)
          ((adicCompletion.equiv K Q) x)) := rfl

theorem adicCompletionMap_comp {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hr : r.asIdeal.LiesOver q.asIdeal)
    (hQ : r.asIdeal.LiesOver Q.asIdeal) :
    (Commons.RingTheory.Henselian.adicCompletionMap q r hr).comp
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq) =
      Commons.RingTheory.Henselian.adicCompletionMap Q r hQ := by
  have hmap := completionMapRingHom_comp (K := K) (L := L) (M := M) Q q r hq hr hQ
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, adicCompletionMap_apply_def, adicCompletionMap_apply_def,
    adicCompletionMap_apply_def, RingEquiv.apply_symm_apply, ← hmap]
  rfl

end Commons.NumberTheory.NumberField.Completion
