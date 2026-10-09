/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# From Gassmann equivalence of fixing subgroups to an isomorphism of fields

Reference: arXiv:2601.01251, §6 (*Weak Neukirch–Uchida*), last step of the proof of
`thm:uchida isomorphism`: Gassmann equivalence of the subgroups `Gal(L/K_i) ≤ Gal(L/ℚ)` makes them
conjugate, and conjugate subgroups correspond to isomorphic subfields.
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

open IntermediateField

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The pointwise action of `MulAut G` on `Subgroup G` is `Subgroup.map`. -/
theorem mulAut_smul_eq_map (H : Subgroup G) (g : G) :
    (MulAut.conj g) • H = H.map (MulAut.conj g : G →* G) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨(MulAut.conj g)⁻¹ x, hx, MulEquiv.apply_symm_apply (MulAut.conj g) x⟩
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    exact MulEquiv.symm_apply_apply (MulAut.conj g) y

/-- **Conjugate fixing subgroups give an isomorphism of the fixed fields.**

If `K₁` and `K₂` are intermediate fields of a finite Galois extension `L/ℚ` whose fixing subgroups
are conjugate in `Gal(L/ℚ)`, then `K₁` and `K₂` are isomorphic. -/
theorem nonempty_ringEquiv_of_fixingSubgroup_map_conj {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (K₁ K₂ : IntermediateField ℚ L) {g : Gal(L/ℚ)}
    (h : K₁.fixingSubgroup.map (MulAut.conj g : Gal(L/ℚ) →* Gal(L/ℚ)) = K₂.fixingSubgroup) :
    Nonempty (↥K₁ ≃+* ↥K₂) := by
  have hK : K₁.map (g : L →ₐ[ℚ] L) = K₂ := by
    have hfix : (K₁.map (g : L →ₐ[ℚ] L)).fixingSubgroup = K₂.fixingSubgroup := by
      rw [IsGalois.map_fixingSubgroup, mulAut_smul_eq_map, h]
    have h2 := congrArg IntermediateField.fixedField hfix
    rwa [IsGalois.fixedField_fixingSubgroup, IsGalois.fixedField_fixingSubgroup] at h2
  refine ⟨RingEquiv.ofBijective
    ({ toFun := fun x => ⟨g x, by rw [← hK]; exact (IntermediateField.mem_map K₁).mpr ⟨x, x.2, rfl⟩⟩
       map_one' := by ext; simp
       map_mul' := by intro x y; ext; simp
       map_zero' := by ext; simp
       map_add' := by intro x y; ext; simp } : ↥K₁ →+* ↥K₂) ?_⟩
  constructor
  · intro x y hxy
    have h1 : (g x : L) = (g y : L) := congrArg Subtype.val hxy
    exact Subtype.ext (g.injective h1)
  · intro y
    have hy : (y : L) ∈ K₁.map (g : L →ₐ[ℚ] L) := by rw [hK]; exact y.2
    obtain ⟨x, hxK, hxg⟩ := (IntermediateField.mem_map K₁).mp hy
    refine ⟨⟨x, hxK⟩, ?_⟩
    ext
    simpa using hxg

/-- **Gassmann equivalence of the fixing subgroups gives an isomorphism of the fields.**

This is the final step of Uchida's weak Neukirch–Uchida theorem: the arithmetic input produces
Gassmann equivalence of `Gal(L/K₁)` and `Gal(L/K₂)` inside `Gal(L/ℚ)` for a common finite Galois
`L/ℚ`, and the group-theoretic step (`conj_eq_of_gassmann`) turns this into an isomorphism of the
two subfields. -/
theorem nonempty_ringEquiv_of_gassmann {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (K₁ K₂ : IntermediateField ℚ L) {ℓ : ℕ}
    [Fact ℓ.Prime]
    (h₁ : IsGassmannEquivalent (ZMod ℓ) K₁.fixingSubgroup K₂.fixingSubgroup)
    (h₂ : IsGassmannEquivalent (ZMod ℓ) K₂.fixingSubgroup K₁.fixingSubgroup) :
    Nonempty (↥K₁ ≃+* ↥K₂) := by
  obtain ⟨g, hg⟩ :=
    conj_eq_of_gassmann (ZMod ℓ) K₁.fixingSubgroup K₂.fixingSubgroup h₁ h₂
  exact nonempty_ringEquiv_of_fixingSubgroup_map_conj K₁ K₂ hg

/-- **Gassmann equivalence of the fixing subgroups of two embeddings into a common Galois
field gives an isomorphism of the sources.** -/
theorem nonempty_ringEquiv_of_gassmann_fieldRange {K₁ K₂ L : Type*} [Field K₁] [Field K₂]
    [Field L] [Algebra ℚ K₁] [Algebra ℚ K₂] [Algebra ℚ L] [NumberField L] [IsGalois ℚ L]
    {ℓ : ℕ} [Fact ℓ.Prime] (i : K₁ →ₐ[ℚ] L) (j : K₂ →ₐ[ℚ] L)
    (h₁ : IsGassmannEquivalent (ZMod ℓ) (i.fieldRange).fixingSubgroup (j.fieldRange).fixingSubgroup)
    (h₂ : IsGassmannEquivalent (ZMod ℓ) (j.fieldRange).fixingSubgroup (i.fieldRange).fixingSubgroup) :
    Nonempty (K₁ ≃+* K₂) := by
  obtain ⟨e⟩ :=
    nonempty_ringEquiv_of_gassmann (i.fieldRange) (j.fieldRange) (ℓ := ℓ) h₁ h₂
  exact ⟨(AlgEquiv.ofInjective i i.injective).toRingEquiv.trans
    (e.trans (AlgEquiv.ofInjective j j.injective).toRingEquiv.symm)⟩

end NK.UchidaKummer
