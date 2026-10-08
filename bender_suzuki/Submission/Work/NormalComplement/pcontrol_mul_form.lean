import Mathlib
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem pcontrol_mul_form {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E W : Subgroup G} (h : Work.NormalComplement.IsPControl p E W) {U : Subgroup G}
    (hU : U ≤ E) (hUp : IsPGroup p U) {x : G} (hxW : x ∈ W)
    (hconj : Submission.Blueprint.conj x⁻¹ U ≤ E) :
    ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧
      ∃ e ∈ E, x = c * e := by
  obtain ⟨c, hc, he⟩ := h.2.2 U hU hUp x hxW hconj
  exact ⟨c, hc.1, hc.2, he⟩

end Work.NormalComplement
