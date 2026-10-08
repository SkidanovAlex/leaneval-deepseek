import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.DoubleCoset

/-- In a finite group, if `g = b₁ * w * b₂` with `b₁, b₂ ∈ B`, then `g` and `w` give
conjugate intersections: `B ⊓ B^g` is the conjugate by `b₁` of `B ⊓ B^w`, hence they have
the same cardinality. -/
theorem card_inf_map_conj_eq_of_mem_doubleCoset {G : Type*} [Group G] [Finite G] (B : Subgroup G) (w b₁ b₂ g : G) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hg : g = b₁ * w * b₂) : Nat.card ↥(B ⊓ B.map (MulAut.conj g).toMonoidHom) = Nat.card ↥(B ⊓ B.map (MulAut.conj w).toMonoidHom) := by
  have key : B ⊓ B.map (MulAut.conj g).toMonoidHom =
      (B ⊓ B.map (MulAut.conj w).toMonoidHom).map (MulAut.conj b₁).toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxB, hxM⟩ := hx
      rw [Subgroup.mem_map] at hxM
      obtain ⟨y, hyB, hyx⟩ := hxM
      rw [Subgroup.mem_map]
      refine ⟨b₁⁻¹ * x * b₁, ?_, ?_⟩
      · rw [Subgroup.mem_inf]
        constructor
        · exact B.mul_mem (B.mul_mem (B.inv_mem hb₁) hxB) hb₁
        · rw [Subgroup.mem_map]
          refine ⟨b₂ * y * b₂⁻¹, B.mul_mem (B.mul_mem hb₂ hyB) (B.inv_mem hb₂), ?_⟩
          rw [← hyx]
          change (MulAut.conj w) (b₂ * y * b₂⁻¹) = b₁⁻¹ * ((MulAut.conj g) y) * b₁
          rw [MulAut.conj_apply, MulAut.conj_apply, hg]
          group
      · change (MulAut.conj b₁) (b₁⁻¹ * x * b₁) = x
        rw [MulAut.conj_apply]; group
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨z, hzD, hzx⟩ := hx
      rw [Subgroup.mem_inf] at hzD
      obtain ⟨hzB, hzM⟩ := hzD
      rw [Subgroup.mem_map] at hzM
      obtain ⟨y, hyB, hyz⟩ := hzM
      rw [Subgroup.mem_inf]
      constructor
      · rw [← hzx]
        change b₁ * z * b₁⁻¹ ∈ B
        exact B.mul_mem (B.mul_mem hb₁ hzB) (B.inv_mem hb₁)
      · rw [Subgroup.mem_map]
        refine ⟨b₂⁻¹ * y * b₂, B.mul_mem (B.mul_mem (B.inv_mem hb₂) hyB) hb₂, ?_⟩
        rw [← hzx, ← hyz]
        change (MulAut.conj g) (b₂⁻¹ * y * b₂) = (MulAut.conj b₁) ((MulAut.conj w) y)
        rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, hg]
        group
  rw [key]
  exact Subgroup.card_map_of_injective (MulAut.conj b₁).injective

end Commons.GroupTheory.DoubleCoset