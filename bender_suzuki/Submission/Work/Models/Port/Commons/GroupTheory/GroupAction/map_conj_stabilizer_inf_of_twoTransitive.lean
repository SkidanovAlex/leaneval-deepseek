import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

theorem map_conj_stabilizer_inf_of_twoTransitive {G Ω : Type*} [Group G] [MulAction G Ω]
    (h : MulAction.IsMultiplyPretransitive G Ω 2) {a b c d : Ω} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : G, (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b).map
      (MulAut.conj g).toMonoidHom = MulAction.stabilizer G c ⊓ MulAction.stabilizer G d := by
  rw [MulAction.is_two_pretransitive_iff] at h
  obtain ⟨g, hga, hgb⟩ := h hab hcd
  refine ⟨g, ?_⟩
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj g a, hga,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj g b, hgb]

end Commons.GroupTheory.GroupAction