import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

theorem TIInfBot {F : Type*} [Group F] (K P : Subgroup F)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹) = ⊥) :
    K ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hdisj := hTI x hx.1 hx1
  have hmem : x ∈ P ⊓ P.map (MulAut.conj x⁻¹) := by
    refine ⟨hx.2, ?_⟩
    exact Subgroup.mem_map.mpr ⟨x, hx.2, by simp⟩
  rw [hdisj] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

end Work.BSLit.Wielandt
