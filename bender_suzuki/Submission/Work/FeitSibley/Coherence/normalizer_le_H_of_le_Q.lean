import Mathlib
import Submission.Work.FeitSibley.Basic
import Submission.Work.FeitSibley.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

/-- Any nontrivial subgroup `P` of the T.I. subgroup `Q` has its normalizer contained in
`H`: if `x ∈ N_G(P)` then `P ≤ Q ∩ Qˣ`, and since `P ≠ ⊥` the T.I. property forces
`x ∈ H`. -/
theorem normalizer_le_H_of_le_Q {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {P : Subgroup G} (hP : P ≤ h.Q) (hPne : P ≠ ⊥) :
    Subgroup.normalizer (P : Set G) ≤ h.H := by
  intro x hx
  by_contra hxH
  have hbot : h.Q ⊓ Submission.Blueprint.conj x h.Q = ⊥ := h.Q_TI x hxH
  have hPle : P ≤ h.Q ⊓ Submission.Blueprint.conj x h.Q := by
    intro p hp
    refine Subgroup.mem_inf.mpr ⟨hP hp, ?_⟩
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * p * x, ?_, ?_⟩
    · have h1 : p ∈ P ↔ x⁻¹ * p * x ∈ P := by
        simpa using Subgroup.mem_normalizer_iff.mp (inv_mem hx) p
      exact hP (h1.mp hp)
    · show x * (x⁻¹ * p * x) * x⁻¹ = p
      group
  rw [hbot] at hPle
  exact hPne (le_bot_iff.mp hPle)

end Work.FeitSibley.Coherence
