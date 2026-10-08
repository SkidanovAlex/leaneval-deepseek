import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.faithfulSMul_coset_iff_core_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

/-- The action of a group `G` on the quotient `G ⧸ H` by left multiplication is
faithful exactly when the normal core of `H` is trivial.

This is the `GroupAction`-namespace restatement of
`Commons.GroupTheory.Subgroup.faithfulSMul_coset_iff_core_bot`: the kernel of the
natural action of `G` on its left coset space `G ⧸ H` is the intersection of all
conjugates of `H`, i.e. the normal core `H.normalCore`. -/
theorem faithfulSMul_quotient_iff {G : Type*} [Group G] (H : Subgroup G) :
    FaithfulSMul G (G ⧸ H) ↔ H.normalCore = ⊥ :=
  Commons.GroupTheory.Subgroup.faithfulSMul_coset_iff_core_bot H

end Commons.GroupTheory.GroupAction
