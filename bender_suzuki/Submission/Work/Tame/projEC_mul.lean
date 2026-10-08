import Mathlib
import Submission.Work.Tame.Tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- `projEC` is multiplicative: this is the content of `𝔑 = 𝔎(𝔏 ∩ 𝔑)` with `𝔎` normal in `𝔑`,
and it is what makes the inflation `α_{i1}` of (9.4) a class function.  Given `N₁ = H₁M₁` and
`N₂ = H₂M₂` with `H_j ∈ 𝔎`, `M_j ∈ 𝔏 ⊓ 𝔑`, one has
`N₁N₂ = (H₁·M₁H₂M₁⁻¹)·(M₁M₂)`, and `𝔎 ⊴ 𝔑` gives `M₁H₂M₁⁻¹ ∈ 𝔎`. -/
theorem projEC_mul {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (N₁ N₂ : ↥(Lgrp (K : Set X))) :
    projEC Lhat K (N₁ * N₂) = projEC Lhat K N₁ * projEC Lhat K N₂ := by
  -- the projections `M_j = projEC N_j` satisfy `N_j M_j⁻¹ ∈ K` (Feit–Thompson (ii)(c))
  have h1 : (N₁ : X) * ((projEC Lhat K N₁ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹ ∈ K :=
    mul_projEC_inv_mem hsup N₁
  have h2 : (N₂ : X) * ((projEC Lhat K N₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹ ∈ K :=
    mul_projEC_inv_mem hsup N₂
  -- `𝔎` is normal in `𝔑 = N(𝔎)`, so conjugation by `N₁` preserves `K`
  have hmem : (N₁ : X) ∈ Subgroup.normalizer (K : Set X) := N₁.2
  have hnorm : (N₁ : X) * ((N₂ : X) *
      ((projEC Lhat K N₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹) * (N₁ : X)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hmem _).mp h2
  -- hence the product of the projections is a valid projection of `N₁N₂`
  have hkey : ((N₁ * N₂ : ↥(Lgrp (K : Set X))) : X) *
      ((projEC Lhat K N₁ * projEC Lhat K N₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹ ∈ K := by
    have heq : ((N₁ * N₂ : ↥(Lgrp (K : Set X))) : X) *
        ((projEC Lhat K N₁ * projEC Lhat K N₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹
        = ((N₁ : X) * ((N₂ : X) *
            ((projEC Lhat K N₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹) * (N₁ : X)⁻¹) *
          ((N₁ : X) * ((projEC Lhat K N₁ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [heq]
    exact K.mul_mem hnorm h1
  -- uniqueness of the projection (`K ⊓ 𝔏 = ⊥`) finishes
  exact projEC_eq_of hinf hkey

end Work.Tame
