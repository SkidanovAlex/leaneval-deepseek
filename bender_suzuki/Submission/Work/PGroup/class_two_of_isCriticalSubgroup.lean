import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- The commutator subgroup of a critical subgroup `C` is contained in its center: since `C ≤ P`
we have `[C, C] ≤ [P, C]`, and `[P, C] ≤ Z(C)` is the commutator-in-center axiom of
`IsCriticalSubgroup`.  Consequently `C` has nilpotency class at most two. -/
theorem class_two_of_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ} (P C : Subgroup G)
    (hC : Work.PGroup.IsCriticalSubgroup p P C) : ⁅C, C⁆ ≤ Work.PGroup.centerIn C :=
  le_trans (Subgroup.commutator_mono hC.le_self le_rfl) hC.commutator_le_center

end Work.PGroup
