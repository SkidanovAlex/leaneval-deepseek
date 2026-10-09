import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local
import Submission.Commons.NumberTheory.NumberField.Completion.le_natCard_quotient_units_range_norm_of_abelian_local
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

theorem natCard_quotient_units_range_norm_eq_card_of_abelian_local
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) =
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
  have hle := natCard_quotient_units_range_norm_le_finrank_of_abelian_local Q hcomm
  have hge := le_natCard_quotient_units_range_norm_of_abelian_local Q hcomm
  have hcard : Nat.card (E ≃ₐ[Q.adicCompletion K] E) =
      Module.finrank (Q.adicCompletion K) E :=
    IsGalois.card_aut_eq_finrank (Q.adicCompletion K) E
  rw [hcard]
  exact le_antisymm hle hge

end Commons.NumberTheory.NumberField.Completion
