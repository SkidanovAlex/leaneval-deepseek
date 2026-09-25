/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gassmann equivalence of the `I_H`-submodules implies conjugacy of the subgroups

Reference: arXiv:2601.01251, §6 (*Weak Neukirch–Uchida*), final step of the proof of
`thm:uchida isomorphism`.
-/

import Submission.NK.UchidaKummer.Gassmann.Basic

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

open MonoidAlgebra

variable {G : Type*} [Group G]

/-- **Gassmann equivalence** of the submodules `I_{H₁}R[G]^{H₁}` and `I_{H₂}R[G]^{H₂}`
(`R[G]^{H₁}` meaning the `H₁`-indexed direct power, as in §6 of the paper).

Every element of the direct power `I_{H₁}R[G]^{H₁}` can be translated by some `g ∈ G` into
`I_{H₂}R[G]^{H₂}`. -/
def IsGassmannEquivalent (R : Type*) [CommRing R] (H₁ H₂ : Subgroup G) : Prop :=
  ∀ f : H₁ → MonoidAlgebra R G, (∀ h : H₁, f h ∈ IH R H₁) →
    ∃ g : G, ∀ h : H₁, MonoidAlgebra.single g (1 : R) * f h ∈ IH R H₂

variable (R : Type*) [CommRing R]

/-- `single h 1 - single 1 1 ∈ I_H` for `h ∈ H`. -/
theorem single_sub_one_mem_IH (H : Subgroup G) (h : H) :
    MonoidAlgebra.single (h : G) (1 : R) - MonoidAlgebra.single 1 (1 : R) ∈ IH R H := by
  have := single_mul_sub_single_mem_IH R H h 1
  rw [mul_one] at this
  exact this

/-- **The Gassmann hypothesis forces `conj_g H₁ ≤ H₂`** for some `g ∈ G` (Uchida's argument),
in elementwise form: some `g` conjugates every element of `H₁` into `H₂`. -/
theorem exists_conj_mem_of_gassmann [Nontrivial R] (H₁ H₂ : Subgroup G)
    (hgass : IsGassmannEquivalent R H₁ H₂) :
    ∃ g : G, ∀ y ∈ H₁, g * y * g⁻¹ ∈ H₂ := by
  obtain ⟨g, hg⟩ := hgass (fun h : H₁ => MonoidAlgebra.single (h : G) (1 : R)
      - MonoidAlgebra.single 1 (1 : R)) (fun h => single_sub_one_mem_IH R H₁ h)
  refine ⟨g, fun y hy => ?_⟩
  have hy' := hg ⟨y, hy⟩
  rw [mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
    mul_one, mul_one] at hy'
  obtain ⟨k, hk⟩ := exists_mul_eq_of_mem_IH R H₂ hy'
  have hk' : (k : G) = g * y * g⁻¹ := by rw [hk, mul_assoc, mul_inv_cancel, mul_one]
  exact hk' ▸ k.2

/-- **The Gassmann hypothesis forces `conj_g H₁ ≤ H₂`** for some `g ∈ G` (Uchida's argument). -/
theorem conj_le_of_gassmann [Nontrivial R] (H₁ H₂ : Subgroup G)
    (hgass : IsGassmannEquivalent R H₁ H₂) :
    ∃ g : G, H₁.map (MulAut.conj g : G →* G) ≤ H₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_gassmann R H₁ H₂ hgass
  refine ⟨g, fun x hx => ?_⟩
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change g * y * g⁻¹ ∈ H₂
  exact hg y hy

/-- A cardinality estimate: `conj_k H₂ ≤ H₁` forces `|H₂| ≤ |H₁|`. -/
theorem card_le_of_map_conj_le [Fintype G] (H₁ H₂ : Subgroup G) {k : G}
    (hk : H₂.map (MulAut.conj k : G →* G) ≤ H₁) : Nat.card H₂ ≤ Nat.card H₁ := by
  have hcard : Nat.card (H₂.map (MulAut.conj k : G →* G)) = Nat.card H₂ :=
    Subgroup.card_map_of_injective (f := (MulAut.conj k : G →* G)) (MulAut.conj k).injective
  rw [← hcard]
  exact Nat.card_mono (Set.toFinite _) (fun x hx => hk hx)

/-- **Gassmann equivalence in both directions implies conjugacy of the subgroups.** -/
theorem conj_eq_of_gassmann [Fintype G] [Nontrivial R] (H₁ H₂ : Subgroup G)
    (h₁ : IsGassmannEquivalent R H₁ H₂) (h₂ : IsGassmannEquivalent R H₂ H₁) :
    ∃ g : G, H₁.map (MulAut.conj g : G →* G) = H₂ := by
  obtain ⟨g, hg⟩ := conj_le_of_gassmann R H₁ H₂ h₁
  obtain ⟨k, hk⟩ := conj_le_of_gassmann R H₂ H₁ h₂
  have hcard : Nat.card H₂ ≤ Nat.card H₁ := card_le_of_map_conj_le H₁ H₂ hk
  have hcardg : Nat.card (H₁.map (MulAut.conj g : G →* G)) = Nat.card H₁ :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g : G →* G)) (MulAut.conj g).injective
  exact ⟨g, Subgroup.eq_of_le_of_card_ge hg (by rw [hcardg]; exact hcard)⟩

/-- The elementwise form of `conj_eq_of_gassmann`. -/
theorem exists_conj_eq_of_gassmann [Fintype G] [Nontrivial R] (H₁ H₂ : Subgroup G)
    (h₁ : IsGassmannEquivalent R H₁ H₂) (h₂ : IsGassmannEquivalent R H₂ H₁) :
    ∃ g : G, ∀ y ∈ H₁, g * y * g⁻¹ ∈ H₂ := by
  obtain ⟨g, hg⟩ := conj_eq_of_gassmann R H₁ H₂ h₁ h₂
  refine ⟨g, fun y hy => ?_⟩
  have hmem : (MulAut.conj g : G ≃* G) y ∈ H₂ := by
    rw [← hg]
    exact (Subgroup.mem_map (f := (MulAut.conj g : G →* G))).mpr ⟨y, hy, rfl⟩
  change g * y * g⁻¹ ∈ H₂
  exact hmem

end NK.UchidaKummer
