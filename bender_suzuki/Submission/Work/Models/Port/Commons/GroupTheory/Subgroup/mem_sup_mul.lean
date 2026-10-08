import Mathlib.Algebra.Group.Subgroup.Pointwise

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem mem_sup_mul {G : Type*} [Group G] (H K : Subgroup G)
    (h : K ≤ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H K h] at hx'
  rw [Set.mem_mul] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

end Commons.GroupTheory.Subgroup
