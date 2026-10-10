import Mathlib.FieldTheory.Galois.Infinite
import Submission.NK.LocalCFT.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois-correspondence property of the local norm group

For the canonical local Artin reciprocity datum `D : ArtinReciprocity F F'`
(`NK.LocalCFT.Basic`), the norm groups `N_{L/F} Lˣ ⊆ Fˣ` of the finite abelian levels
`L ≤ F^{ab}` are *order-reversing* in `L`, and quite sharply so:

  `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ ↔ L₂ ≤ L₁`.

This is the elementary half of the Galois correspondence for local class field theory: the datum
already gives, at every finite abelian level `L`, a *surjection* `Fˣ ↠ Gal(L/F)` with kernel
`N_{L/F} Lˣ` (`ArtinReciprocity.isLevelIso`).

* `⇐` (`L₂ ≤ L₁ ⟹ N_{L₁} ≤ N_{L₂}`): the Artin map at the smaller level is the Artin map at the
  larger one followed by restriction (`AlgEquiv.restrictNormal`), so its kernel contains the
  kernel at the larger level.
* `⇒`: if `N_{L₁} ≤ N_{L₂}`, then on the compositum `K = L₁ ⊔ L₂` every `F`-automorphism of `K`
  fixing `L₁` lifts along the *surjective* Artin map `Fˣ ↠ Gal(K/F)`, and the resulting
  computation shows that it fixes `L₂`; the Galois correspondence in `F^{ab}/F` then gives
  `L₂ ≤ L₁`.  (Here one uses that `K/F` is finite abelian — it is a quotient of the abelian
  `Gal(F^{ab}/F)` — so that the level isomorphism of the datum is available at `K`.)

Only the level isomorphisms of the datum are used; the `cofinal` field (the existence theorem) is
not needed.
-/

set_option linter.style.haveILetI false

namespace NK.LocalCFT.NormGroup

open scoped Classical

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- An element of `Gal(F^{ab}/F)` restricts to `1` at the level `L` if and only if it fixes every
element of `L`. -/
lemma levelRestrict_eq_one_iff
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')) [Normal F L]
    (σ : AbGal F F') :
    levelRestrict L σ = 1 ↔ ∀ x ∈ L, σ x = x := by
  rw [levelRestrict, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply]
  exact AlgEquiv.restrictNormal_eq_one_iff L σ

/-- **The norm groups of the finite abelian levels are order-reversing in the level:**
`N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ ↔ L₂ ≤ L₁`. -/
theorem normGroup_le_iff {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
    (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) :
    NK.LocalReciprocity.normGroup F ↥L₁ ≤ NK.LocalReciprocity.normGroup F ↥L₂ ↔ L₂ ≤ L₁ := by
  constructor
  · -- **`⇒`**  Assume `N(L₁) ≤ N(L₂)`; we must show `L₂ ≤ L₁`.
    intro hN
    -- The compositum `K = L₁ ⊔ L₂` is a finite abelian level.
    haveI hKfd : FiniteDimensional F ↥(L₁ ⊔ L₂) := inferInstance
    haveI hKn : Normal F ↥(L₁ ⊔ L₂) := inferInstance
    -- `Gal(K/F)` is abelian: it is a quotient of the abelian group `Gal(F^{ab}/F)`.
    have hKc : ∀ σ τ : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂), σ * τ = τ * σ := by
      intro σ τ
      obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥(L₁ ⊔ L₂))
        (E := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) σ
      obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥(L₁ ⊔ L₂))
        (E := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) τ
      rw [← map_mul, ← map_mul, NK.LocalReciprocity.commutative_gal_maxAbelianSubext σ' τ']
    -- Every `F`-automorphism of `K` fixing `L₁` pointwise fixes `L₂` pointwise.
    have hfix : L₁.fixingSubgroup ≤ L₂.fixingSubgroup := by
      intro σ hσ
      have hσ' : ∀ x ∈ L₁, σ x = x := (IntermediateField.mem_fixingSubgroup_iff L₁ σ).mp hσ
      -- lift `σ` along the surjective Artin map at the level `K`
      obtain ⟨a, ha⟩ := (D.isLevelIso (L₁ ⊔ L₂) hKc).1 (levelRestrict (L₁ ⊔ L₂) σ)
      rw [MonoidHom.comp_apply] at ha
      -- the "correction" `τ = artin a * σ⁻¹` fixes `K` pointwise (it lies in `Gal(K/K)`)
      have hτK : levelRestrict (L₁ ⊔ L₂) (D.artin a * σ⁻¹) = 1 := by
        rw [map_mul, map_inv, ha]
        exact mul_inv_cancel _
      have hτ' : ∀ x ∈ (L₁ ⊔ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')),
          (D.artin a * σ⁻¹) x = x :=
        (levelRestrict_eq_one_iff (L₁ ⊔ L₂) (D.artin a * σ⁻¹)).mp hτK
      have hτmem : (D.artin a * σ⁻¹) ∈ L₂.fixingSubgroup :=
        (IntermediateField.mem_fixingSubgroup_iff L₂ _).mpr fun x hx =>
          hτ' x ((show L₂ ≤ (L₁ ⊔ L₂ : IntermediateField F
            (NK.LocalReciprocity.maxAbelianSubext F F')) from le_sup_right) hx)
      -- `artin a` fixes `L₁` pointwise, hence by hypothesis its norm group class lies in `N(L₂)`
      have hDa₁ : ∀ x ∈ L₁, D.artin a x = x := by
        intro x hx
        have hxK : x ∈ (L₁ ⊔ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')) :=
          (show L₁ ≤ (L₁ ⊔ L₂ : IntermediateField F
            (NK.LocalReciprocity.maxAbelianSubext F F')) from le_sup_left) hx
        calc D.artin a x = (D.artin a * σ⁻¹) (σ x) := by
              rw [AlgEquiv.mul_apply, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply]
          _ = (D.artin a * σ⁻¹) x := by rw [hσ' x hx]
          _ = x := hτ' x hxK
      have hDamem : D.artin a ∈ L₂.fixingSubgroup := by
        have hmem₁ : a ∈ NK.LocalReciprocity.normGroup F ↥L₁ := by
          rw [← (D.isLevelIso L₁ h₁).2, MonoidHom.mem_ker, MonoidHom.comp_apply,
            levelRestrict_eq_one_iff L₁ (D.artin a)]
          exact hDa₁
        have hmem₂ : a ∈ NK.LocalReciprocity.normGroup F ↥L₂ := hN hmem₁
        rw [← (D.isLevelIso L₂ h₂).2, MonoidHom.mem_ker, MonoidHom.comp_apply,
          levelRestrict_eq_one_iff L₂ (D.artin a)] at hmem₂
        exact (IntermediateField.mem_fixingSubgroup_iff L₂ (D.artin a)).mpr hmem₂
      -- `σ = τ⁻¹ * artin a` is a product of two elements fixing `L₂`
      have hσeq : σ = (D.artin a * σ⁻¹)⁻¹ * D.artin a := by group
      rw [hσeq]
      exact mul_mem (inv_mem hτmem) hDamem
    -- Galois correspondence in `F^{ab}/F`: `L₂ ≤ fixedField (Gal(F^{ab}/L₁)) = L₁`
    have hle : L₂ ≤ IntermediateField.fixedField L₁.fixingSubgroup :=
      (IntermediateField.le_iff_le L₁.fixingSubgroup L₂).mpr hfix
    rwa [InfiniteGalois.fixedField_fixingSubgroup L₁] at hle
  · -- **`⇐`**  Assume `L₂ ≤ L₁`; the Artin map at `L₂` is the Artin map at `L₁` followed by
    -- restriction, so its kernel contains `N(L₁)`.
    intro hle a ha
    rw [← (D.isLevelIso L₁ h₁).2] at ha
    rw [← (D.isLevelIso L₂ h₂).2]
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha ⊢
    rw [levelRestrict_eq_one_iff L₁ (D.artin a)] at ha
    rw [levelRestrict_eq_one_iff L₂ (D.artin a)]
    exact fun x hx => ha x (hle hx)

end NK.LocalCFT.NormGroup
