import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

theorem natCard_groupCohomology_two_units_eq_card_of_cyclic_arbitrary_base
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E] [IsCyclic (E ≃ₐ[B] E)] :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) = Nat.card (E ≃ₐ[B] E) := by
  classical
  letI : CommGroup (E ≃ₐ[B] E) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[B] E)
  calc Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
      = Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits B E) 0) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
          g hg _
    _ = Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) :=
        Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units B E
    _ = Nat.card (E ≃ₐ[B] E) :=
        natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base Q

end Commons.NumberTheory.NumberField.Completion
