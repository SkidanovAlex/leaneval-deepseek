import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem mem_comap_center_iff {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {x : G} :
    x ∈ (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N) ↔ ∀ g : G, g * x * g⁻¹ * x⁻¹ ∈ N := by
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, Subgroup.mem_center_iff]
  constructor
  · intro hx g
    rw [← QuotientGroup.eq_one_iff]
    rw [show (↑(g * x * g⁻¹ * x⁻¹) : G ⧸ N) = (↑g) * (↑x) * (↑g)⁻¹ * (↑x)⁻¹ by simp]
    rw [hx (↑g)]
    group
  · intro hx y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg := hx g
    rw [← QuotientGroup.eq_one_iff] at hg
    rw [show (↑(g * x * g⁻¹ * x⁻¹) : G ⧸ N) = (↑g) * (↑x) * (↑g)⁻¹ * (↑x)⁻¹ by simp] at hg
    have h1 : (↑g : G ⧸ N) * ↑x * (↑g)⁻¹ = ↑x := by
      have h2 : (↑g : G ⧸ N) * ↑x * (↑g)⁻¹ * (↑x)⁻¹ * ↑x = 1 * ↑x := by rw [hg]
      simpa using h2
    have h4 := congrArg (fun z => z * (↑g : G ⧸ N)) h1
    simpa using h4

end Work.Higman
