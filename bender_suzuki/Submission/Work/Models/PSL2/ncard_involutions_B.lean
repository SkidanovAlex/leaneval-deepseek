import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.involutions_B
import Submission.Work.Models.PSL2.U_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.PSL2

theorem ncard_involutions_B {F : Type*} [Field F] [CharP F 2] [Finite F] :
    (Submission.Blueprint.involutions
        ((Work.Models.PSL2.B (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F))).ncard
      = Nat.card F - 1 := by
  rw [involutions_B]
  -- the involutions of `B` are the non-trivial elements of the unipotent radical `U`
  have hset : {x : Work.Models.SL2 F | x ∈ U (F := F) ∧ x ≠ 1}
      = (U (F := F) : Set (Work.Models.SL2 F)) \ {1} := by
    ext x; simp
  rw [hset, Set.ncard_sdiff (by simp : ({1} : Set (Work.Models.SL2 F)) ⊆ (U (F := F) : Set _))]
  rw [Set.ncard_singleton]
  have hU : ((U (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F)).ncard
      = Nat.card ↥(U (F := F)) := rfl
  rw [hU, card_U]

end Work.Models.PSL2
