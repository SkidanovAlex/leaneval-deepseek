import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic

namespace NK.NUV2.LC.RouteB

open IsDedekindDomain

theorem index_localNormSubgroup_of_localDeg_eq_prime {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (p : ℕ) (hp : p.Prime)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hloc : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) = p) :
    (MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q Q hq)).index = p := by
  letI : Algebra (Q.adicCompletion F) (q.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hcard : Nat.card (q.adicCompletion E ≃ₐ[Q.adicCompletion F] q.adicCompletion E) = p := by
    rw [Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq, hloc]
  haveI : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic (q.adicCompletion E ≃ₐ[Q.adicCompletion F] q.adicCompletion E) :=
    isCyclic_of_prime_card hcard
  have hnorm := Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic
    Q q hq hcyc
  letI : CommGroup (q.adicCompletion E ≃ₐ[Q.adicCompletion F] q.adicCompletion E) :=
    hcyc.commGroup
  have hab : Nat.card (Abelianization
      (q.adicCompletion E ≃ₐ[Q.adicCompletion F] q.adicCompletion E)) = p := by
    rw [← Nat.card_congr (Abelianization.equivOfComm
      (H := q.adicCompletion E ≃ₐ[Q.adicCompletion F] q.adicCompletion E)).toEquiv]
    exact hcard
  rw [Subgroup.index_eq_card]
  rw [show MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q Q hq) =
      MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion F) :
        q.adicCompletion E →* Q.adicCompletion F)) from rfl]
  rw [hnorm, hab]

end NK.NUV2.LC.RouteB
