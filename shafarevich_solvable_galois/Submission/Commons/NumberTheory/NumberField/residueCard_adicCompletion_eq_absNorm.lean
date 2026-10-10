import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

/-- The residue field of the ring of integers of the `v`-adic completion of a number field `K`
has cardinality equal to the absolute norm of the prime ideal `v`: this is the degree of the
residue field extension `𝓞 K / v` over the prime field, i.e. the inertia degree of `v`. -/
theorem residueCard_adicCompletion_eq_absNorm {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)) =
      Ideal.absNorm v.asIdeal := by
  obtain ⟨e⟩ := adicCompletion_residueField_equiv_exists v
  exact Nat.card_congr e.toEquiv

end Commons.NumberTheory.NumberField
