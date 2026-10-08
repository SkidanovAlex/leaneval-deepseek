import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.DoubleCoset

theorem exists_map_conj_eq_inf_map_conj_of_doubleCoset_cover {G : Type*} [Group G]
    (T B : Subgroup G) (w : G)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G))
    (hinf : B ⊓ B.map (MulAut.conj w).toMonoidHom = T) {g : G} (hg : g ∉ B) :
    ∃ x : G, B ⊓ B.map (MulAut.conj g).toMonoidHom = T.map (MulAut.conj x).toMonoidHom := by
  rcases hcover g with hgB | ⟨b₁, b₂, hg_eq⟩
  · exact absurd hgB hg
  · refine ⟨(b₁ : G), ?_⟩
    have hb1 : (b₁ : G) ∈ B := b₁.2
    have hb2 : (b₂ : G) ∈ B := b₂.2
    rw [hg_eq, ← hinf]
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨hyB, x, hxB, hxy⟩
      refine ⟨(b₁ : G)⁻¹ * y * (b₁ : G),
        ⟨mul_mem (mul_mem (inv_mem hb1) hyB) hb1,
         (b₂ : G) * x * (b₂ : G)⁻¹, mul_mem (mul_mem hb2 hxB) (inv_mem hb2), ?_⟩, ?_⟩
      · rw [← hxy]; group
      · group
    · rintro ⟨t, ⟨htB, z, hzB, hzt⟩, hty⟩
      refine ⟨?_, (b₂ : G)⁻¹ * z * (b₂ : G),
        mul_mem (mul_mem (inv_mem hb2) hzB) hb2, ?_⟩
      · rw [← hty]; exact mul_mem (mul_mem hb1 htB) (inv_mem hb1)
      · rw [← hty, ← hzt]; group

end Commons.GroupTheory.DoubleCoset