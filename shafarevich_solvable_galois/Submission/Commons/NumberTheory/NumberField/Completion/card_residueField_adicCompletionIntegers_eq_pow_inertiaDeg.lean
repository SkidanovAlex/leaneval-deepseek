import Mathlib
import Submission.Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField

namespace Commons.NumberTheory.NumberField.Completion

/-- The residue field of the ring of integers of the `p`-adic completion of `ℚ`, where `p` is a
prime number generating the prime ideal `Q0.asIdeal` of `𝓞 ℚ`, has exactly `p` elements. -/
theorem residueCard_adicCompletionIntegers_rat
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal) :
    Nat.card (IsLocalRing.ResidueField (Q0.adicCompletionIntegers ℚ)) = p := by
  rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm Q0,
    asIdeal_eq_span_prime Q0 p hp hmem, Ideal.absNorm_span_natCast,
    RingOfIntegers.rank ℚ, Module.finrank_self, pow_one]

theorem card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal) (K : Type*)
    [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) :
    Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) =
      p ^ (Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)) := by
  rw [Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
    ℚ K Q0 Q hQ, residueCard_adicCompletionIntegers_rat Q0 p hp hmem]

end Commons.NumberTheory.NumberField.Completion
