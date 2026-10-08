import Mathlib

set_option linter.unusedVariables false

namespace Work.BG

theorem mapSubgroupOfEqSubgroupOfSubgroupOf {G : Type} [Group G] {M K L : Subgroup G}
    (hMK : M ≤ K) (hKL : K ≤ L) :
    (M.subgroupOf K).map (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom =
      (M.subgroupOf L).subgroupOf (K.subgroupOf L) := by
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
  rw [MulEquiv.symm_symm]
  simp only [Subgroup.subgroupOfEquivOfLe]
  rfl

end Work.BG
