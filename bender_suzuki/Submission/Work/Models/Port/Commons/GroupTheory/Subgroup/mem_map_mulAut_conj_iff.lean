import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem mem_map_mulAut_conj_iff {G : Type*} [Group G] (H : Subgroup G) (g : G) (y : G) :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]
    exact hx
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩

end Commons.GroupTheory.Subgroup