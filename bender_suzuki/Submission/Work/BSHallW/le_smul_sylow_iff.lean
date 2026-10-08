import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSHallW

/-- Membership criterion: `A ≤ g • S` (the conjugate Sylow subgroup) holds exactly when the
pointwise conjugation of `A` by `g⁻¹` is contained in `S`. Both sides say, elementwise, that
`g⁻¹ a g ∈ S` for every `a ∈ A`. -/
theorem le_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} (S : Sylow p G) (g : G)
    (A : Subgroup G) :
    A ≤ ((g • S : Sylow p G) : Subgroup G) ↔
      A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul]
  constructor
  · intro h a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨b, hbA, rfl⟩ := ha
    have h1 : (MulAut.conj g)⁻¹ • b ∈ (S : Subgroup G) := by
      have := h hbA
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    rw [← MonoidHom.map_inv MulAut.conj g] at h1
    simpa using h1
  · intro h a ha
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [← MonoidHom.map_inv MulAut.conj g]
    exact h (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ha)

end Work.BSHallW
