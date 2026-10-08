import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem map_conj_eq_of_mem {G : Type*} [Group G] (M : Subgroup G) {g : G} (hg : g ∈ M) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  apply le_antisymm
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨m, hm, rfl⟩
    change g * m * g⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hg hm) (M.inv_mem hg)
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

end Commons.GroupTheory.StronglyEmbedded