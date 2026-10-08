import Mathlib
import Submission.Work.FeitSibley.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

/-- Auxiliary algebra step: the conjugated equality `d₁ y d₁⁻¹ = d₂ y d₂⁻¹` implies that
`d₂⁻¹ d₁` fixes `y` (by conjugation). -/
private theorem conj_eq_one_of_conj_eq {G : Type} [Group G] {d₁ d₂ y : G}
    (heq : d₁ * y * d₁⁻¹ = d₂ * y * d₂⁻¹) :
    (d₂⁻¹ * d₁) * y * (d₂⁻¹ * d₁)⁻¹ = y := by
  have h3 : d₂⁻¹ * (d₁ * y * d₁⁻¹) * d₂ = y := by rw [heq]; group
  rw [mul_inv_rev, inv_inv]
  simpa only [mul_assoc] using h3

theorem conj_map_injOn_of_fpf {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {A : Subgroup G} (hA : A ≤ h.Q1) {y : G} (hy : y ∈ A) (hy1 : y ≠ 1) :
    Set.InjOn (fun d : G => d * y * d⁻¹) (h.D : Set G) := by
  intro d₁ hd₁ d₂ hd₂ heq
  have hyQ1 : y ∈ h.Q1 := hA hy
  have hc : d₂⁻¹ * d₁ ∈ h.D := h.D.mul_mem (h.D.inv_mem hd₂) hd₁
  have hfix : (d₂⁻¹ * d₁) * y * (d₂⁻¹ * d₁)⁻¹ = y := conj_eq_one_of_conj_eq heq
  by_cases hne : d₂⁻¹ * d₁ = 1
  · exact (inv_mul_eq_one.mp hne).symm
  · exact absurd (h.D_fpf_Q1 (d₂⁻¹ * d₁) hc hne y hyQ1 hfix) hy1

end Work.FeitSibley.Coherence
