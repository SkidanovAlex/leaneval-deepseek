import Mathlib.GroupTheory.Frattini
import Submission.Commons.GroupTheory.Nilpotent.isNilpotent_of_forall_isCoatom_normal
import Submission.Commons.GroupTheory.QuotientGroup.isSimpleGroup_quotient_of_coatom

namespace Commons.GroupTheory.Nilpotent

open Subgroup

/-- A finite group is nilpotent if and only if its commutator subgroup lies in its Frattini
subgroup. -/
theorem isNilpotent_iff_commutator_le_frattini {G : Type*} [Group G] [Finite G] :
    Group.IsNilpotent G ↔ commutator G ≤ frattini G := by
  constructor
  · intro hG
    have hnorm : ∀ M : Subgroup G, IsCoatom M → M.Normal :=
      ((Group.isNilpotent_of_finite_tfae (G := G)).out 1 3).mp hG
    have hle : ∀ M : Subgroup G, IsCoatom M → commutator G ≤ M := by
      intro M hM
      have : M.Normal := hnorm M hM
      have : IsSimpleGroup (G ⧸ M) :=
        Commons.GroupTheory.QuotientGroup.isSimpleGroup_quotient_of_coatom M hM
      have : Group.IsNilpotent (G ⧸ M) := inferInstance
      have : IsMulCommutative (G ⧸ M) := inferInstance
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    rw [frattini, Order.radical]
    exact le_iInf fun M => le_iInf fun hM => hle M hM
  · intro h
    refine isNilpotent_of_forall_isCoatom_normal fun M hM => ?_
    exact Subgroup.Normal.of_commutator_le G (h.trans (frattini_le_coatom hM))

end Commons.GroupTheory.Nilpotent