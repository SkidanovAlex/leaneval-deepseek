import Mathlib

namespace Work.Tower.CyclotomicBase

theorem fixedField_iInf_eq_iSup {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] {ι : Type*} [Fintype ι] (H : ι → Subgroup Gal(E/F)) :
    IntermediateField.fixedField (⨅ i, H i) = ⨆ i, IntermediateField.fixedField (H i) := by
  apply le_antisymm
  · rw [← IsGalois.fixedField_fixingSubgroup (⨆ i, IntermediateField.fixedField (H i))]
    apply IntermediateField.fixedField_le
    apply le_iInf
    intro j
    exact (IntermediateField.fixingSubgroup_le
      (le_iSup (fun i => IntermediateField.fixedField (H i)) j)).trans
      (le_of_eq (IntermediateField.fixingSubgroup_fixedField (H j)))
  · apply iSup_le
    intro j
    apply IntermediateField.fixedField_le
    exact iInf_le H j

end Work.Tower.CyclotomicBase
