import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Galois
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

open IsDedekindDomain

open scoped Pointwise

theorem exists_frobenius_galRestrict {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hP : P.asIdeal.LiesOver p.asIdeal) :
    ∃ σ : Gal(L/K),
      Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
          NumberField.RingOfIntegers L) P.asIdeal = P.asIdeal ∧
      ∀ x : NumberField.RingOfIntegers L,
        Ideal.Quotient.mk P.asIdeal
            (galRestrict (NumberField.RingOfIntegers K) K L
              (NumberField.RingOfIntegers L) σ x) =
          (Ideal.Quotient.mk P.asIdeal x) ^ (Nat.card ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)) := by
  letI act : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hcomm : SMulCommClass Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    ⟨fun g a x => by
      change galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) g
          (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a * x) =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a *
          galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) g x
      rw [map_mul, AlgEquiv.commutes]⟩
  haveI hinv : Algebra.IsInvariant (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) Gal(L/K) :=
    Algebra.isInvariant_of_isGalois (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hfinS : Finite (NumberField.RingOfIntegers L ⧸ P.asIdeal) :=
    finite_quotient_heightOneSpectrum P
  obtain ⟨σ, hσ⟩ :=
    IsArithFrobAt.exists_of_isInvariant (NumberField.RingOfIntegers K) (Gal(L/K)) P.asIdeal
  refine ⟨σ, ?_, ?_⟩
  · have hmem : σ ∈ MulAction.stabilizer Gal(L/K) P.asIdeal := IsArithFrobAt.mem_stabilizer hσ
    rw [MulAction.mem_stabilizer_iff] at hmem
    rwa [show σ • P.asIdeal = Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
      NumberField.RingOfIntegers L) P.asIdeal from rfl] at hmem
  · intro x
    have hx := hσ.mk_apply x
    rw [show P.asIdeal.under (NumberField.RingOfIntegers K) = p.asIdeal from hP.over.symm] at hx
    change Ideal.Quotient.mk P.asIdeal (σ • x) =
      (Ideal.Quotient.mk P.asIdeal x) ^ Nat.card ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)
    exact hx

end Commons.NumberTheory.NumberField