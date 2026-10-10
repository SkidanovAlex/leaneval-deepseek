import Mathlib.FieldTheory.Galois.Infinite
import Submission.NK.LocalReciprocity.Invariants
import Submission.NK.LocalReciprocity.LubinTate
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.LocalInputs.AbelianRank

/-- **The fixing subgroup of the fixed field of `H` is the (Krull-)closure of `H`.** -/
theorem fixingSubgroup_fixedField_eq_topologicalClosure {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsGalois F E] (H : Subgroup Gal(E/F)) :
    (IntermediateField.fixedField H).fixingSubgroup = H.topologicalClosure := by
  refine le_antisymm ?_ ?_
  · have h2 : (IntermediateField.fixedField H).fixingSubgroup ≤
        (IntermediateField.fixedField H.topologicalClosure).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le
        (IntermediateField.fixedField_le (Subgroup.le_topologicalClosure H))
    have h3 : (IntermediateField.fixedField H.topologicalClosure).fixingSubgroup =
        H.topologicalClosure :=
      InfiniteGalois.fixingSubgroup_fixedField
        (⟨H.topologicalClosure, Subgroup.isClosed_topologicalClosure H⟩ : ClosedSubgroup Gal(E/F))
    exact le_trans h2 (le_of_eq h3)
  · refine Subgroup.topologicalClosure_minimal H ?_ (InfiniteGalois.fixingSubgroup_isClosed _)
    exact (IntermediateField.le_iff_le H (IntermediateField.fixedField H)).mp le_rfl

end NK.LocalInputs.AbelianRank
