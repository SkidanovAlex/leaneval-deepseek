import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_union_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Set identifications between `pdRelSub` and `pdTr`

`pdRelSub W K = {y : W | (y : M) ∉ K}` is the complement, inside the subtype `W`, of the
"trace" `pdTr W K = {y : W | (y : M) ∈ K}` (`pd_union_aux.lean`).  These two descriptions are used
interchangeably when the `A+B` complexes (which kill chains in `W∖K`) are compared with the
abstract-space versions of the crux lemmas (which speak of `Kᶜ`).  We record the identifications
here so that the rewrites in `pd_union_split` are one-liners.

Note the two dictionary entries needed for the A+B sequence with `A = pdRelSub W K`,
`B = pdRelSub W L`:

* `A ∩ B = pdRelSub W (K ∪ L)`  (`pdRelSub_union`) — the third slot;
* `A ∪ B = pdRelSub W (K ∩ L)`  (`pdRelSub_union_sub`) — the `A ∪ B` slot of `pdABInclRel`;
* `(pdRelSub W K)ᶜ = pdTr W K`   (`pdRelSub_eq_compl_pdTr`) — the killed set seen in the space.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-- `pdRelSub W K` is the complement in `W` of `pdTr W K`. -/
theorem pdRelSub_eq_compl_pdTr (W K : Set M) : pdRelSub W K = (pdTr W K)ᶜ := by
  ext x; rfl

/-- The relative subset of a union is the intersection of the relative subsets. -/
theorem pdRelSub_union (W K L : Set M) : pdRelSub W (K ∪ L) = pdRelSub W K ∩ pdRelSub W L := by
  ext x
  simp only [pdRelSub, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union,
    not_or]

/-- The union of the relative subsets is the relative subset of the intersection. -/
theorem pdRelSub_union_sub (W K L : Set M) : pdRelSub W K ∪ pdRelSub W L = pdRelSub W (K ∩ L) := by
  ext x
  simp only [pdRelSub, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_inter_iff,
    not_and_or]

/-- `pdTr W (U \ L) = pdTr W U \ pdTr W L`. -/
theorem pdTr_sdiff (W U L : Set M) : pdTr W (U \ L) = pdTr W U \ pdTr W L := by
  ext x
  simp only [pdTr, Set.mem_setOf_eq, Set.mem_sdiff]

/-- `pdTr W (U ∩ V) = pdTr W U ∩ pdTr W V`. -/
theorem pdTr_inter (W U V : Set M) : pdTr W (U ∩ V) = pdTr W U ∩ pdTr W V := by
  ext x
  simp only [pdTr, Set.mem_setOf_eq, Set.mem_inter_iff]

/-- The union of the traces is the trace of the union. -/
theorem pdTr_union (W U V : Set M) : pdTr W U ∪ pdTr W V = pdTr W (U ∪ V) := by
  ext x
  simp only [pdTr, Set.mem_setOf_eq, Set.mem_union]

/-- `pdTr W U ∪ pdTr W V = univ` when `U ∪ V = univ` on the ambient space `M`. -/
theorem pdTr_union_eq_univ (W U V : Set M) (h : U ∪ V = Set.univ) :
    pdTr W U ∪ pdTr W V = (Set.univ : Set W) := by
  rw [pdTr_union, h]
  ext x; trivial

end

end Work.Cohomology
