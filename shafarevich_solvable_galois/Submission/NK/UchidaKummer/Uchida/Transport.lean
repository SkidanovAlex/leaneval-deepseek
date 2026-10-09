/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The transport step of §6: from Uchida's module data to the Gassmann condition

Reference: arXiv:2601.01251, §6, proof of `thm:uchida isomorphism`.

Uchida's embedding problem produces an extension `N / L` (with `N / ℚ` Galois) whose Galois group
`Λ = Gal(N/L)` is, as a `Gal(L/ℚ)`-module, isomorphic to `𝔽_ℓ[G]^n` (`G = Gal(L/ℚ)`), together with
subfields `M_i` whose Galois groups `J_i = Gal(N/M_i)` correspond to the submodules
`I_{H_i}𝔽_ℓ[G]^n`.  The arithmetic input (`cor:arith equiv` + Gassmann/Perlis) says that every
element of `J₁` is conjugate in `Gal(N/ℚ)` into `J₂` (and conversely).

This file proves the purely group-theoretic transport: from that conjugacy statement and the
identification of the `J_i` with the `I_{H_i}`-submodules, one gets Uchida's Gassmann condition,
whose consequence (`conj_le_of_gassmannOf` below) is `conj_g H₁ ⊆ H₂` — and symmetrically.
-/

import Submission.NK.UchidaKummer.Gassmann.GassmannEquivalent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

open MonoidAlgebra

variable {G Γ : Type*} [Group G] [Group Γ]

/-- **The Gassmann condition with an arbitrary index type.**  For the index type `n`, every
`n`-tuple of elements of `I_{H₁}R[G]` can be translated by some `g ∈ G` into `I_{H₂}R[G]`.

For `n = H₁` this is §6's condition
(`NK.UchidaKummer.IsGassmannEquivalent`).  The general form is what Uchida's embedding problem
provides (`𝔽_ℓ[G]^n` for an arbitrary `n`). -/
def IsGassmannEquivalentOf (R : Type*) [CommRing R] (n : Type*) (H₁ H₂ : Subgroup G) : Prop :=
  ∀ f : n → MonoidAlgebra R G, (∀ i : n, f i ∈ IH R H₁) →
    ∃ g : G, ∀ i : n, MonoidAlgebra.single g (1 : R) * f i ∈ IH R H₂

variable (R : Type*) [CommRing R]

/-- `IsGassmannEquivalent` is the case `n = H₁` of `IsGassmannEquivalentOf`. -/
theorem isGassmannEquivalent_iff_isGassmannEquivalentOf_self (H₁ H₂ : Subgroup G) :
    IsGassmannEquivalent R H₁ H₂ ↔ IsGassmannEquivalentOf R H₁ H₁ H₂ :=
  Iff.rfl

/-- **The transport step of §6.**

`ρ : Γ →* G` is the restriction map `Gal(N/ℚ) →* Gal(L/ℚ)` (so `Γ = Gal(N/ℚ)`, `G = Gal(L/ℚ)`,
`ρ.ker = Gal(N/L)`), `e` identifies `Gal(N/L)` with the module `𝔽_ℓ[G]^n` of §6 (in a `Γ`-equivariant
way, `he`), and `J₁`, `J₂` are the subgroups corresponding to the submodules
`I_{H₁}𝔽_ℓ[G]^n`, `I_{H₂}𝔽_ℓ[G]^n` (`hJ₁e`, `hJ₂e`).

If every element of `J₁` is conjugate in `Γ` into `J₂` (`hconj`), then Uchida's Gassmann condition
`IsGassmannEquivalentOf R n H₁ H₂` holds. -/
theorem isGassmannEquivalentOf_of_module_data {n : ℕ} {ℓ : ℕ}
    (ρ : Γ →* G) (H₁ H₂ : Subgroup G)
    (e : ↥ρ.ker ≃ (Fin n → MonoidAlgebra (ZMod ℓ) G))
    (he : ∀ (γ : Γ) (x : ↥ρ.ker),
      e ((MulAut.conjNormal γ) x) = fun i => MonoidAlgebra.single (ρ γ) (1 : ZMod ℓ) * e x i)
    (J₁ J₂ : Subgroup Γ) (hJ₁ : J₁ ≤ ρ.ker) (hJ₂ : J₂ ≤ ρ.ker)
    (hJ₁e : ∀ f : Fin n → MonoidAlgebra (ZMod ℓ) G,
      f ∈ e '' (J₁.subgroupOf ρ.ker : Set ↥ρ.ker) ↔ ∀ i, f i ∈ IH (ZMod ℓ) H₁)
    (hJ₂e : ∀ f : Fin n → MonoidAlgebra (ZMod ℓ) G,
      f ∈ e '' (J₂.subgroupOf ρ.ker : Set ↥ρ.ker) ↔ ∀ i, f i ∈ IH (ZMod ℓ) H₂)
    (hconj : ∀ x ∈ J₁, ∃ γ : Γ, γ * x * γ⁻¹ ∈ J₂) :
    IsGassmannEquivalentOf (ZMod ℓ) (Fin n) H₁ H₂ := by
  intro f hf
  have hmem : f ∈ e '' (J₁.subgroupOf ρ.ker : Set ↥ρ.ker) := (hJ₁e f).mpr hf
  obtain ⟨x, hx, rfl⟩ := hmem
  obtain ⟨γ, hγ⟩ := hconj (x : Γ) hx
  refine ⟨ρ γ, fun i => ?_⟩
  have hker : γ * (x : Γ) * γ⁻¹ ∈ ρ.ker := hJ₂ hγ
  have hmem₂ : e ⟨γ * (x : Γ) * γ⁻¹, hker⟩
      ∈ e '' (J₂.subgroupOf ρ.ker : Set ↥ρ.ker) :=
    ⟨⟨γ * (x : Γ) * γ⁻¹, hker⟩, (Subgroup.mem_subgroupOf (H := J₂) (K := ρ.ker)).mpr hγ, rfl⟩
  have hval : ∀ i, (e ⟨γ * (x : Γ) * γ⁻¹, hker⟩) i ∈ IH (ZMod ℓ) H₂ :=
    (hJ₂e _).mp hmem₂
  have hEq : e ⟨γ * (x : Γ) * γ⁻¹, hker⟩
      = fun i => MonoidAlgebra.single (ρ γ) (1 : ZMod ℓ) * e x i := by
    rw [show (⟨γ * (x : Γ) * γ⁻¹, hker⟩ : ↥ρ.ker) = (MulAut.conjNormal γ) x from
      Subtype.ext (MulAut.conjNormal_apply γ x).symm]
    exact he γ x
  rw [hEq] at hval
  exact hval i

/-- **The λ-argument of §6.**  If the Gassmann condition holds with an index type containing `H₁`
(so that the element `λ = Σ_h (h - 1)e_h` of §6 can be formed), then some `g ∈ G` conjugates `H₁`
into `H₂`. -/
theorem conj_le_of_gassmannOf {ℓ : ℕ} [Nontrivial (ZMod ℓ)] {n : ℕ} {H₁ H₂ : Subgroup G}
    (inj : H₁ ↪ Fin n) (h : IsGassmannEquivalentOf (ZMod ℓ) (Fin n) H₁ H₂) :
    ∃ g : G, H₁.map (MulAut.conj g : G →* G) ≤ H₂ := by
  classical
  set lam : Fin n → MonoidAlgebra (ZMod ℓ) G :=
    fun i => if hi : ∃ h : H₁, inj h = i then
        MonoidAlgebra.single (((Classical.choose hi : H₁) : G)) (1 : ZMod ℓ)
          - MonoidAlgebra.single 1 (1 : ZMod ℓ) else 0 with hlamdef
  have hlammem : ∀ i : Fin n, lam i ∈ IH (ZMod ℓ) H₁ := by
    intro i
    by_cases hi : ∃ h : H₁, inj h = i
    · rw [hlamdef]
      simp only [dif_pos hi]
      exact single_sub_one_mem_IH (ZMod ℓ) H₁ (Classical.choose hi)
    · rw [hlamdef]
      simp only [dif_neg hi]
      exact Submodule.zero_mem _
  obtain ⟨g, hg⟩ := h lam hlammem
  refine ⟨g, fun x hx => ?_⟩
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change g * y * g⁻¹ ∈ H₂
  have hyi : ∃ h : H₁, inj h = inj ⟨y, hy⟩ := ⟨⟨y, hy⟩, rfl⟩
  have hval := hg (inj ⟨y, hy⟩)
  rw [hlamdef] at hval
  simp only [dif_pos hyi] at hval
  simp only [mul_sub, MonoidAlgebra.single_mul_single, mul_one] at hval
  have hch : ((Classical.choose hyi : H₁) : G) = y :=
    congrArg (fun z : H₁ => (z : G)) (inj.injective (Classical.choose_spec hyi))
  rw [hch] at hval
  obtain ⟨k, hk⟩ := exists_mul_eq_of_mem_IH (ZMod ℓ) H₂ hval
  have hk' : (k : G) = g * y * g⁻¹ := by rw [hk, mul_assoc, mul_inv_cancel, mul_one]
  exact hk' ▸ k.2

end NK.UchidaKummer
