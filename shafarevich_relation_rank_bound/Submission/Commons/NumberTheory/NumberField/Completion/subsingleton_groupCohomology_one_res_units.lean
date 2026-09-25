import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian

namespace Commons.NumberTheory.NumberField.Completion

theorem subsingleton_groupCohomology_one_res_units
    {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) :
    Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1) := by
  have hr : Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E) =
      Rep.res (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) E) := rfl
  rw [hr]
  exact (NatCardP9.subsingleton_groupCohomology_res_mulEquiv
    (IntermediateField.subgroupEquivAlgEquiv H)
    (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) E) 1).2 inferInstance

end Commons.NumberTheory.NumberField.Completion
