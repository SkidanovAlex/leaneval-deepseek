import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Basic

theorem hasNormalPComplement_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (h : IsPGroup p G) : Work.NPC.HasNormalPComplement p G := by
  -- If `G` is a `p`-group then the trivial subgroup is a normal `p`-complement:
  -- its order is `1`, coprime to `p`, and the quotient `G ⧸ ⊥` is a `p`-group.
  refine ⟨⊥, ⟨Subgroup.normal_bot, ?_, ?_⟩⟩
  · simp
  · exact h.to_quotient ⊥

end Work.NPC.Basic
