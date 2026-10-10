import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.sha2_hasse.Gateway
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.sha2_hasse

variable {k : Type} [Field k] [NumberField k]

theorem exists_valuationSubring_at_prime_of_heightOneSpectrum
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (Lf L))) :
    ∃ (A : ValuationSubring (AlgebraicClosure k))
      (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)),
      A.comap (algebraMap (Lf L) (AlgebraicClosure k)) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (Lf L) q ∧
      A.comap (algebraMap k (AlgebraicClosure k)) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p := by
  obtain ⟨A, hA⟩ := Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
    (K := Lf L) (K' := AlgebraicClosure k) q
  refine ⟨A, ⟨q.asIdeal.under (𝓞 k), inferInstance, Ideal.under_ne_bot (𝓞 k) q.ne_bot⟩, hA, ?_⟩
  rw [show A.comap (algebraMap k (AlgebraicClosure k)) =
      (A.comap (algebraMap (Lf L) (AlgebraicClosure k))).comap (algebraMap k (Lf L)) from by
    rw [ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq k (Lf L) (AlgebraicClosure k)],
    hA]
  exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime (K := k) (L := Lf L)
    ⟨q.asIdeal.under (𝓞 k), inferInstance, Ideal.under_ne_bot (𝓞 k) q.ne_bot⟩ q
    (Ideal.over_under q.asIdeal)


theorem placeOf_asIdeal_liesOver
    (L E : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (hLE : (L : IntermediateField k (AlgebraicClosure k)) ≤
      (E : IntermediateField k (AlgebraicClosure k)))
    [Algebra (Lf L) (Lf E)] [IsScalarTower k (Lf L) (Lf E)]
    [IsScalarTower (Lf L) (Lf E) (AlgebraicClosure k)]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring (AlgebraicClosure k))
    (hA : A.comap (algebraMap k (AlgebraicClosure k)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (Lf L)))
    (hAq : A.comap (algebraMap (Lf L) (AlgebraicClosure k)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (Lf L) q) :
    (Submission.NeukirchUchida.Local.placeOf p A hA
        (E : IntermediateField k (AlgebraicClosure k))).asIdeal.LiesOver q.asIdeal := by
  have hW := Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf p A hA
    (E : IntermediateField k (AlgebraicClosure k))
  have hcomap : A.comap (algebraMap (Lf L) (AlgebraicClosure k)) =
      (A.comap (algebraMap (Lf E) (AlgebraicClosure k))).comap (algebraMap (Lf L) (Lf E)) := by
    rw [ValuationSubring.comap_comap,
      IsScalarTower.algebraMap_eq (Lf L) (Lf E) (AlgebraicClosure k)]
  have h1 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (Lf E)
        (Submission.NeukirchUchida.Local.placeOf p A hA
          (E : IntermediateField k (AlgebraicClosure k)))).comap (algebraMap (Lf L) (Lf E)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (Lf L) q := by
    rw [← hW, ← hcomap]
    exact hAq
  let W := Submission.NeukirchUchida.Local.placeOf p A hA (E : IntermediateField k (AlgebraicClosure k))
  let q' : IsDedekindDomain.HeightOneSpectrum (𝓞 (Lf L)) :=
    ⟨W.asIdeal.under (𝓞 (Lf L)), inferInstance, Ideal.under_ne_bot (𝓞 (Lf L)) W.ne_bot⟩
  have h2 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (Lf E) W).comap
      (algebraMap (Lf L) (Lf E)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (Lf L) q' :=
    Commons.RingTheory.Valuation.comap_valuationSubringAtPrime (K := Lf L) (L := Lf E)
      q' W (Ideal.over_under W.asIdeal)
  have heq : q' = q :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (R := 𝓞 (Lf L)) (K := Lf L)
      (by rw [← h2, h1])
  exact ⟨(congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal heq).symm⟩


end Work.SSGRoute.sha2_hasse
