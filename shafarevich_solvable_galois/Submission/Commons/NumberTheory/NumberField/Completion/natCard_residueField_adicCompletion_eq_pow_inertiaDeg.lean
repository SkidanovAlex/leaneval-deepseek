import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- The residue field of the ring of integers of the `V`-adic completion of a number field `K`
has the same cardinality as the residue field `𝓞 K / V.asIdeal` of `V`. -/
theorem natCard_residueField_adicCompletionIntegers_eq_natCard_quotient
    (K : Type*) [Field K] [NumberField K]
    (V : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField (V.adicCompletionIntegers K)) =
      Nat.card ((NumberField.RingOfIntegers K) ⧸ V.asIdeal) := by
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists V
  exact Nat.card_congr e.toEquiv

theorem natCard_residueField_adicCompletion_eq_pow_inertiaDeg (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) =
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))) ^
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  -- the residue field of the completion is the residue field of the original place
  have hA : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) =
      Nat.card ((NumberField.RingOfIntegers L) ⧸ q.asIdeal) :=
    natCard_residueField_adicCompletionIntegers_eq_natCard_quotient L q
  have hB : Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) =
      Nat.card ((NumberField.RingOfIntegers K) ⧸ Q.asIdeal) :=
    natCard_residueField_adicCompletionIntegers_eq_natCard_quotient K Q
  -- the inertia degree is the degree of the residue field extension
  letI : Field ((NumberField.RingOfIntegers K) ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  have hC : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      Module.finrank ((NumberField.RingOfIntegers K) ⧸ Q.asIdeal)
        ((NumberField.RingOfIntegers L) ⧸ q.asIdeal) :=
    Ideal.inertiaDeg_eq_of_isMaximal Q.asIdeal q.asIdeal
  -- a finite-dimensional vector space over a finite field has cardinality `q ^ dim`
  have hD : Nat.card ((NumberField.RingOfIntegers L) ⧸ q.asIdeal) =
      Nat.card ((NumberField.RingOfIntegers K) ⧸ Q.asIdeal) ^
        Module.finrank ((NumberField.RingOfIntegers K) ⧸ Q.asIdeal)
          ((NumberField.RingOfIntegers L) ⧸ q.asIdeal) :=
    Module.natCard_eq_pow_finrank
  rw [hA, hB, hC]
  exact hD

end Commons.NumberTheory.NumberField.Completion
