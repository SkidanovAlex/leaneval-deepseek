import Mathlib
import Submission.Work.FeitSibley.Defs
import Submission.Work.FeitSibley.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

open scoped commutatorElement

/-- Since `Q = S · Q₁` with `S` and `Q₁` commuting elementwise, the commutator of `S` with the
whole of `Q` is already the commutator of `S` with itself: any `q ∈ Q` splits as a product
`a * b` with `a ∈ S`, `b ∈ Q₁`, and the `Q₁`-part contributes nothing. -/
theorem commutator_S_Q_le_commutator_S_S {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) :
    ⁅h.S, h.Q⁆ ≤ ⁅h.S, h.S⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_Q_decomp hg₂
  -- `b ∈ Q₁` commutes with `g₁ ∈ S`, so it drops out of the commutator.
  have hcomm : g₁ * b = b * g₁ := h.commute g₁ hg₁ b hb
  have hcb : ⁅g₁, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have key : ⁅g₁, a * b⁆ = ⁅g₁, a⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hcb]
    simp
  rw [key]
  exact Subgroup.commutator_mem_commutator hg₁ ha

end Work.FeitSibley.Coherence
