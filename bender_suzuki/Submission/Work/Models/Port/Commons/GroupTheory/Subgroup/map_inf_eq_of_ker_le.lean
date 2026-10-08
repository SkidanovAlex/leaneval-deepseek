import Mathlib.Algebra.Group.Subgroup.Ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem map_inf_eq_of_ker_le {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (A B : Subgroup G) (hker : φ.ker ≤ A) :
    Subgroup.map φ (A ⊓ B) = Subgroup.map φ A ⊓ Subgroup.map φ B := by
  refine le_antisymm ?_ ?_
  · exact Subgroup.map_inf_le A B φ
  · intro x hx
    rw [Subgroup.mem_map]
    rcases hx with ⟨hxA, hxB⟩
    rcases Subgroup.mem_map.mp hxA with ⟨a, haA, hax⟩
    rcases Subgroup.mem_map.mp hxB with ⟨b, hbB, hbx⟩
    refine ⟨b, ?_, hbx⟩
    constructor
    · have hker_elem : φ (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hax, hbx]
        simp
      have hk : a⁻¹ * b ∈ φ.ker := (MonoidHom.mem_ker).2 hker_elem
      have hab : a⁻¹ * b ∈ A := hker hk
      have h' : a * (a⁻¹ * b) ∈ A := A.mul_mem haA hab
      simpa using h'
    · exact hbB

end Commons.GroupTheory.Subgroup