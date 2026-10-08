import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem mem_map_conj_iff {G : Type*} [Group G] {A : Subgroup G} {z u : G} :
    u ∈ A.map (MulAut.conj z).toMonoidHom ↔ z⁻¹ * u * z ∈ A := by
  rw [Subgroup.mem_map_equiv]
  simp

end Commons.GroupTheory.StronglyEmbedded