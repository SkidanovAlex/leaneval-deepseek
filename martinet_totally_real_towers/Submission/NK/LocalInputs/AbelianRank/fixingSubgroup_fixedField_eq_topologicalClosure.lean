/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The fixing subgroup of the fixed field of a subgroup is its closure

For a Galois extension `E/F` and an *arbitrary* subgroup `H ≤ Gal(E/F)` of the Galois
group (with the Krull topology, `Mathlib/FieldTheory/KrullTopology.lean`),

  `(IntermediateField.fixedField H).fixingSubgroup = H.topologicalClosure`.

Mathlib has this statement only for *closed* subgroups
(`InfiniteGalois.fixingSubgroup_fixedField`, `FieldTheory/Galois/Infinite.lean:146`).
The general case is the one needed in `NK.LocalInputs.AbelianRank`
(see `Hints.lean` in this directory): for `H = commutator Gal(K'/κ)`, whose algebraic
commutator subgroup need not be closed in the Krull topology, it identifies
`Gal(maxAbelianSubext κ K'/κ)` with `Gal(K'/κ) ⧸ (commutator Gal(K'/κ)).topologicalClosure`
— the *topological* (not the abstract) abelianisation of `Gal(K'/κ)`.

The proof is short and does not need the continuity of the action: `H` is contained in
`(fixedField H).fixingSubgroup`, which is closed, giving `≥`; for `≤` note that
`fixedField H.topologicalClosure ≤ fixedField H`, so by contravariance of `fixingSubgroup`
the group `(fixedField H).fixingSubgroup` is contained in
`(fixedField H.topologicalClosure).fixingSubgroup`, and this is `H.topologicalClosure` by
the closed case of the Galois correspondence.
-/
import Mathlib
import Submission.NK.LocalReciprocity.All

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
