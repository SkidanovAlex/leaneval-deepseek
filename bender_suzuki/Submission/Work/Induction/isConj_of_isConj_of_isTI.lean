import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- **Fusion control for TI subgroups**: if `H` is a self-normalizing TI subgroup and
-- `1 ≠ h₁ ∈ H` is `G`-conjugate to `h₂ ∈ H`, then `h₁` and `h₂` are already conjugate in `H`.
-- Indeed a conjugating element `x` satisfies `x * h₁ * x⁻¹ = h₂ ∈ H` with `h₁ ≠ 1`, hence
-- `x ∈ N_G(H) = H`.
theorem isConj_of_isConj_of_isTI {G : Type*} [Group G] (H : Subgroup G)
    (hTI : Work.Induction.IsTI H) (hN : Work.Induction.normalizer H = H) {h₁ h₂ : H}
    (hh₁ : h₁ ≠ 1) (hc : IsConj (h₁ : G) (h₂ : G)) : IsConj h₁ h₂ := by
  obtain ⟨x, hx⟩ := isConj_iff.mp hc
  -- The conjugating element must already lie in `H`: otherwise
  -- `x * h₁ * x⁻¹ ∈ H ⊓ conj x • H = ⊥`, forcing `h₁ = 1`.
  have hxH : x ∈ H := by
    by_contra hxH
    have hxN : x ∉ Work.Induction.normalizer H := by rwa [hN]
    have hmem2 : x * (h₁ : G) * x⁻¹ ∈ (MulAut.conj x • H : Subgroup G) :=
      by simpa [MulAut.conj_apply] using
        Subgroup.smul_mem_pointwise_smul (h₁ : G) (MulAut.conj x) H h₁.2
    have hmem : x * (h₁ : G) * x⁻¹ ∈ H ⊓ (MulAut.conj x • H : Subgroup G) :=
      ⟨by rw [hx]; exact h₂.2, hmem2⟩
    rw [hTI x hxN] at hmem
    refine hh₁ (Subtype.ext ?_)
    have h2 : x * (h₁ : G) = x := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
    exact mul_left_cancel (show x * (h₁ : G) = x * 1 by simpa using h2)
  -- Hence `x ∈ H` conjugates `h₁` to `h₂` inside `H`.
  refine isConj_iff.mpr ⟨⟨x, hxH⟩, ?_⟩
  apply Subtype.ext
  simpa using hx

end Work.Induction
