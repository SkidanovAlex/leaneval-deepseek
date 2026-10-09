import Mathlib.FieldTheory.Galois.Infinite
import Submission.NeukirchUchida.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Compatibility of the field-side and group-side correspondences

Reference: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*,
2nd ed., Chapter XII, §12.2 (the proof of Theorem 12.2.1).

A base-field-mapping ring isomorphism `σ : K₂' ≃+* K₁'` acts on the two sides
of the Galois correspondence in the same way:

* on **subfields**: an intermediate field `L₂` of `K₂'/K₂` is carried to the
  intermediate field `σ(L₂)` of `K₁'/K₁`;
* on **subgroups**: conjugation by `σ` (the map `conjHomEquiv`) carries
  `Gal(K₁'/σ(L₂))` to `Gal(K₂'/L₂)`.

The main lemma `map_fixingSubgroup_conjHomEquiv` records that these two actions
are compatible: if `σ '' L₂ = L₁` for intermediate fields `L₁ ⊆ K₁'`,
`L₂ ⊆ K₂'`, then `conjHomEquiv hσ` maps the fixing subgroup of `L₁` onto the
fixing subgroup of `L₂`.  This is the computation which, in the proof of
(12.2.1), shows that a base-field-mapping isomorphism realizing the induced
correspondence of finite extensions induces the given isomorphism `ϕ` of
absolute Galois groups.
-/

namespace Submission.NeukirchUchida

open scoped Topology

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [Algebra K₁ K₁'] [Algebra K₂ K₂']

/-- **Compatibility of transport by `σ`.**  If the base-field-mapping ring
isomorphism `σ : K₂' ≃+* K₁'` carries the intermediate field `L₂` onto `L₁`,
then conjugation by `σ` carries the fixing subgroup of `L₁` onto the fixing
subgroup of `L₂`. -/
theorem map_fixingSubgroup_conjHomEquiv {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    (hL : σ '' (L₂ : Set K₂') = (L₁ : Set K₁')) :
    (L₁.fixingSubgroup).map (conjHomEquiv hσ).toMonoidHom = L₂.fixingSubgroup := by
  have aux₁ : ∀ {g : Gal(K₁'/K₁)}, g ∈ L₁.fixingSubgroup →
      conj hσ g ∈ L₂.fixingSubgroup := by
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx₁ : σ x ∈ L₁ := by
      have : σ x ∈ σ '' (L₂ : Set K₂') := ⟨x, hx, rfl⟩
      rwa [hL] at this
    have hfix : g (σ x) = σ x :=
      (IntermediateField.mem_fixingSubgroup_iff L₁ g).mp hg (σ x) hx₁
    rw [conj_apply hσ, hfix, RingEquiv.symm_apply_apply]
  have aux₂ : ∀ {g : Gal(K₂'/K₂)}, g ∈ L₂.fixingSubgroup →
      conj (mapsBase_symm_alg hσ) g ∈ L₁.fixingSubgroup := by
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ σ '' (L₂ : Set K₂') := by rwa [hL]
    rcases hy' with ⟨x, hx, rfl⟩
    have hfix : g x = x := (IntermediateField.mem_fixingSubgroup_iff L₂ g).mp hg x hx
    simp only [conj_apply (mapsBase_symm_alg hσ) g (σ x)]
    rw [RingEquiv.symm_apply_apply, hfix]
    rfl
  ext g
  constructor
  · intro hg
    rcases Subgroup.mem_map.mp hg with ⟨g₁, hg₁, hg₁g⟩
    have hcoe : (conjHomEquiv hσ).toMonoidHom g₁ = conj hσ g₁ := rfl
    rw [hcoe] at hg₁g
    rw [← hg₁g]
    exact aux₁ hg₁
  · intro hg
    refine Subgroup.mem_map.mpr ⟨conj (mapsBase_symm_alg hσ) g, aux₂ hg, ?_⟩
    have hcoe : (conjHomEquiv hσ).toMonoidHom (conj (mapsBase_symm_alg hσ) g)
        = conj hσ (conj (mapsBase_symm_alg hσ) g) := rfl
    rw [hcoe]
    ext x
    rw [conj_apply hσ, conj_apply (mapsBase_symm_alg hσ)]
    simp

/-- **The field-side correspondence is determined by the group-side one.**
This is the converse of `map_fixingSubgroup_conjHomEquiv`: if the conjugation
isomorphism `conjHomEquiv hσ` matches the fixing subgroups of `L₁` and `L₂`,
then `σ` carries `L₂` onto `L₁`.  (Used in the proof of (12.2.1) to show that a
base-field-mapping isomorphism realizing the induced correspondence of finite
extensions induces the given isomorphism `ϕ` of absolute Galois groups.) -/
theorem image_eq_of_map_fixingSubgroup_eq [IsGalois K₁ K₁'] [IsGalois K₂ K₂']
    {σ : K₂' ≃+* K₁'} (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    (hL : (L₁.fixingSubgroup).map (conjHomEquiv hσ).toMonoidHom = L₂.fixingSubgroup) :
    σ '' (L₂ : Set K₂') = (L₁ : Set K₁') := by
  let L₂' : IntermediateField K₂ K₂' :=
    { carrier := σ ⁻¹' (L₁ : Set K₁')
      mul_mem' := fun {x y} hx hy => by
        simpa using L₁.mul_mem hx hy
      one_mem' := by simpa using L₁.one_mem
      add_mem' := fun {x y} hx hy => by
        simpa using L₁.add_mem hx hy
      zero_mem' := by simpa using L₁.zero_mem
      inv_mem' := fun {x} hx => by simpa using L₁.inv_mem hx
      algebraMap_mem' := fun a => by
        have hmem : σ (algebraMap K₂ K₂' a) ∈ (⊥ : IntermediateField K₁ K₁') :=
          mapsBase_mem (algebraMap K₁ K₁') (algebraMap K₂ K₂') hσ ⟨a, rfl⟩
        exact (bot_le : (⊥ : IntermediateField K₁ K₁') ≤ L₁) hmem }
  have hL₂' : σ '' (L₂' : Set K₂') = (L₁ : Set K₁') := by
    show σ '' (σ ⁻¹' (L₁ : Set K₁')) = (L₁ : Set K₁')
    rw [Set.image_preimage_eq _ σ.surjective]
  have hfix : (L₁.fixingSubgroup).map (conjHomEquiv hσ).toMonoidHom = L₂'.fixingSubgroup :=
    map_fixingSubgroup_conjHomEquiv hσ hL₂'
  have heq : L₂.fixingSubgroup = L₂'.fixingSubgroup := hL.symm.trans hfix
  have hL₂eq : L₂ = L₂' := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L₂,
      ← InfiniteGalois.fixedField_fixingSubgroup L₂', heq]
  rw [← hL₂', hL₂eq]

end Submission.NeukirchUchida
