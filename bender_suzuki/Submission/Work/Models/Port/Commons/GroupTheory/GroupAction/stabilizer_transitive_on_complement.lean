import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

theorem stabilizer_transitive_on_complement {G α : Type*} [Group G] [MulAction G α]
    (x : α) [h2 : MulAction.IsMultiplyPretransitive G α 2] :
    ∀ p q : α, p ≠ x → q ≠ x → ∃ g : G, g • x = x ∧ g • p = q := by
  intro p q hp hq
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨g, hgx, hgp⟩ := h2 (Ne.symm hp) (Ne.symm hq)
  exact ⟨g, hgx, hgp⟩

end Commons.GroupTheory.GroupAction