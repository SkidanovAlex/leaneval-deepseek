import Mathlib
import Submission.NK.TameStructureDeep.Tame.galoisData_fixedField_extendScalars_mulEquiv_quotient_ramificationSubgroup

namespace NK.TameStructureDeep.Tame

/-- **The order of the relative Galois group is the relative degree.**

For intermediate fields `T ≤ M` of a Galois extension `E/F`, the quotient
`Gal(E/T) / Gal(E/M)` — which is `Gal(M/T)` — has cardinality (when finite) equal to the degree
`[M : T]`; if `M/T` is infinite dimensional both sides are `0` (`Nat.card` and `Module.finrank`
of an infinite type/rank).

The proof is the defining identity `Subgroup.index H = Nat.card (G ⧸ H)`, the relative index
formula for fixing subgroups `(M.fixingSubgroup.subgroupOf T.fixingSubgroup).index = [M : T]`
(obtained from `finrank_eq_fixingSubgroup_index` after transporting along the change-of-base
isomorphism `IntermediateField.fixingSubgroupEquiv T`), and the fact that the Galois group of the
relative extension `M/T` has order `[M : T]`. -/
theorem natCard_quotient_fixingSubgroup_eq_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] {T M : IntermediateField F E} (hTM : T ≤ M) :
    Nat.card (↥T.fixingSubgroup ⧸ (M.fixingSubgroup).subgroupOf T.fixingSubgroup) =
      Module.finrank ↥T (IntermediateField.extendScalars hTM) := by
  rw [← Subgroup.index_eq_card]
  rw [← Subgroup.index_map_equiv ((M.fixingSubgroup).subgroupOf T.fixingSubgroup)
      (IntermediateField.fixingSubgroupEquiv T)]
  rw [galoisData_map_fixingSubgroupEquiv_subgroupOf hTM]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index E
    (IntermediateField.extendScalars hTM)).symm

end NK.TameStructureDeep.Tame
