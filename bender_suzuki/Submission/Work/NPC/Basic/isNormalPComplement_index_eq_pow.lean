import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Basic

theorem isNormalPComplement_index_eq_pow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N : Subgroup G} (h : Work.NPC.IsNormalPComplement p N) :
    ∃ k : ℕ, N.index = p ^ k := by
  have hN : N.Normal := h.normal
  obtain ⟨k, hk⟩ := h.isPGroup_quotient.exists_card_eq
  exact ⟨k, by rw [Subgroup.index_eq_card, hk]⟩

end Work.NPC.Basic
