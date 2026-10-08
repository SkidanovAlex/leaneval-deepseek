import Mathlib
import Submission.Work.Tame.Tau
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `α_{i1}` is a class function of `𝔑_i` (Feit–Thompson (9.4))

Feit–Thompson (p. 805) build the Dade-type map `τ` of (9.4) out of the projections
`π : 𝔑_i = N(𝔎_i) → 𝔏 ∩ 𝔑_i` of the decompositions `𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)`.  For a class function
`α` of `𝔏 = N(L̂)` they set `α_{i1}(N) = α(π N)`; since `α` is a class function of `𝔏`, this
requires `π` to intertwine conjugation in `𝔑_i` with conjugation in `𝔏`, i.e. that
`π(z N z⁻¹) = π(z) π(N) π(z)⁻¹` for `z, N ∈ 𝔑_i`.  That is multiplicativity of `π`
(`projEC_mul`) together with `π(z⁻¹) = π(z)⁻¹`, and it is what makes `α_{i1}` a class function.

This file proves that statement, `Work.Tame.alphaI1_isClassFun`.  To keep it self-contained we
reprove the two facts about `projEC` that it needs (`projEC_mul_of_sup`, `projEC_one_of_inf`,
`projEC_inv_of_sup`), rather than depending on the (parallel) files `projEC_mul` / `projEC_one`.

The mathematical content of multiplicativity is the standard one: writing `N_j = H_j M_j` with
`H_j ∈ 𝔎` and `M_j ∈ 𝔏 ∩ 𝔑` (which exists by `mul_projEC_inv_mem`, the content of (ii)(c)), one
has `N₁N₂ = (H₁ · M₁H₂M₁⁻¹) · (M₁M₂)` with `H₁ · M₁H₂M₁⁻¹ ∈ 𝔎` because `𝔎 ⊴ 𝔑`, so the
`𝔏 ∩ 𝔑`-component of the product is `M₁M₂`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

universe u

variable {X : Type u} [Group X] [Fintype X]

/-! ## The two facts about `projEC` used -/

/-- `projEC` is multiplicative: given `N₁ = H₁M₁` and `N₂ = H₂M₂` with `H_j ∈ 𝔎`,
`M_j ∈ 𝔏 ⊓ 𝔑`, one has `N₁N₂ = (H₁·M₁H₂M₁⁻¹)·(M₁M₂)` and `𝔎 ⊴ 𝔑` gives
`M₁H₂M₁⁻¹ ∈ 𝔎`, so the `𝔏 ⊓ 𝔑`-component of the product is `M₁M₂`.

(This is the statement of the sibling file `projEC_mul`, repeated here so that this file is
self-contained.) -/
theorem projEC_mul_of_sup {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (N₁ N₂ : ↥(Lgrp (K : Set X))) :
    projEC Lhat K (N₁ * N₂) = projEC Lhat K N₁ * projEC Lhat K N₂ := by
  set m₁ := projEC Lhat K N₁ with hm₁
  set m₂ := projEC Lhat K N₂ with hm₂
  apply projEC_eq_of hinf
  -- `H_j = N_j M_j⁻¹ ∈ 𝔎`
  have h1 : (N₁ : X) * (m₁ : X)⁻¹ ∈ K := by rw [hm₁]; exact mul_projEC_inv_mem hsup N₁
  have h2 : (N₂ : X) * (m₂ : X)⁻¹ ∈ K := by rw [hm₂]; exact mul_projEC_inv_mem hsup N₂
  -- `M₁H₂M₁⁻¹ ∈ 𝔎`, since `M₁ ∈ 𝔑 = N(𝔎)`
  have hconj : (m₁ : X) * ((N₂ : X) * (m₂ : X)⁻¹) * (m₁ : X)⁻¹ ∈ K :=
    (mem_Lgrp.mp m₁.2.2 ((N₂ : X) * (m₂ : X)⁻¹)).mp h2
  have key : (N₁ : X) * (N₂ : X) * ((m₁ * m₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹
      = ((N₁ : X) * (m₁ : X)⁻¹) * ((m₁ : X) * ((N₂ : X) * (m₂ : X)⁻¹) * (m₁ : X)⁻¹) := by
    simp only [Subgroup.coe_mul]
    group
  show (N₁ : X) * (N₂ : X) * ((m₁ * m₂ : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹ ∈ K
  rw [key]
  exact K.mul_mem h1 hconj

/-- `projEC` sends `1` to `1`: `1 = 1 · 1` is a decomposition of the identity, and `𝔎 ⊓ 𝔏 = 1`
gives uniqueness.  (This is the statement of the sibling file `projEC_one`.) -/
theorem projEC_one_of_inf {Lhat : Set X} {K : Subgroup X}
    (hinf : K ⊓ Lgrp Lhat = ⊥) : projEC Lhat K 1 = 1 := by
  apply projEC_eq_of hinf
  show (1 : X) * (1 : X)⁻¹ ∈ K
  rw [mul_inv_cancel]
  exact K.one_mem

/-- `projEC` commutes with inversion: it is multiplicative and sends `1` to `1`. -/
theorem projEC_inv_of_sup {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (N : ↥(Lgrp (K : Set X))) :
    projEC Lhat K N⁻¹ = (projEC Lhat K N)⁻¹ := by
  have h := projEC_mul_of_sup (Lhat := Lhat) (K := K) hsup hinf N N⁻¹
  rw [mul_inv_cancel, projEC_one_of_inf hinf] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- `projEC` intertwines conjugation in `𝔑 = N(𝔎)` with conjugation by `π z ∈ 𝔏 ⊓ 𝔑`:
`π(z N z⁻¹) = π z · π N · (π z)⁻¹`.  This is the computation that makes `α_{i1}` a class
function of `𝔑`. -/
theorem projEC_conj_of_sup {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (z N : ↥(Lgrp (K : Set X))) :
    projEC Lhat K (z * N * z⁻¹)
      = projEC Lhat K z * projEC Lhat K N * (projEC Lhat K z)⁻¹ := by
  rw [projEC_mul_of_sup hsup hinf (z * N) z⁻¹, projEC_mul_of_sup hsup hinf z N,
    projEC_inv_of_sup hsup hinf z]

/-! ## Feit–Thompson (9.4) -/

/-- Feit–Thompson (9.4): `α_{i1}` is a class function of `𝔑_i = N(𝔎_i)`.  Indeed
`α_{i1}(N) = α(π N)` where `π : 𝔑_i → 𝔏 ⊓ 𝔑_i` is the projection of the decomposition
`𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)` (a group homomorphism by `projEC_mul`), and `α` is a class function of `𝔏`. -/
theorem alphaI1_isClassFun {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) {α : ↥(Lgrp Lhat) → ℂ} (hα : CharCore.IsClassFun α) :
    CharCore.IsClassFun (alphaI1LM Lhat K α) := by
  intro g z
  rw [alphaI1LM_apply, alphaI1LM_apply]
  -- `π (z g z⁻¹) = π z · π g · (π z)⁻¹`
  have hkey : projEC Lhat K (z * g * z⁻¹)
      = projEC Lhat K z * projEC Lhat K g * (projEC Lhat K z)⁻¹ :=
    projEC_conj_of_sup hsup hinf z g
  -- transport to `𝔏`: the two sides are conjugate by `π z ∈ 𝔏`
  have hinc : (Subgroup.inclusion inf_le_left (projEC Lhat K (z * g * z⁻¹)) : ↥(Lgrp Lhat))
      = (Subgroup.inclusion inf_le_left (projEC Lhat K z) : ↥(Lgrp Lhat))
        * Subgroup.inclusion inf_le_left (projEC Lhat K g)
        * (Subgroup.inclusion inf_le_left (projEC Lhat K z) : ↥(Lgrp Lhat))⁻¹ := by
    rw [hkey]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
  rw [hinc]
  exact hα (Subgroup.inclusion inf_le_left (projEC Lhat K g))
    (Subgroup.inclusion inf_le_left (projEC Lhat K z))

end Work.Tame
