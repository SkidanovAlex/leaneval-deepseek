import Mathlib
import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalCFT.NilpotentObstruction.commutator_eq_commutator_commutator
import Submission.NK.LocalCFT.NilpotentObstruction.isMulCommutative_of_abelian_sup_commutator_eq_top
import Submission.NK.LocalReciprocity.LubinTate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The nilpotent obstruction to a reciprocity datum into the absolute Galois group

`NK.LocalReciprocity.LocalReciprocityDatum F F'` asks for a single map `artin : Fˣ →* Gal(F'/F)`
whose composite with the restriction to *every* finite abelian level `L ≤ F'` is the reciprocity
isomorphism `Fˣ ⧸ N(L) ≃* Gal(L/F)`.  Its image is therefore an abelian subgroup of `Gal(F'/F)`
surjecting onto `Gal(L/F)` for every finite abelian level `L`.

This file proves that no such datum exists as soon as `F'` contains a finite normal subextension
`M/F` whose Galois group is nilpotent but not commutative.

The mechanism is group theoretic.  Let `G = Gal(M/F)`, let `q : Gal(F'/F) →* G` be the
restriction map and let `B = q(artin(Fˣ)) ≤ G` be the image of the Artin map.  Then

* `B` is commutative (it is a quotient of the commutative group `Fˣ`);
* `B ⊔ [G,G] = ⊤`: the level `L = M^{[G,G]}` is finite over `F` and abelian over `F`, so the
  datum applies to it and exhibits `B` surjecting onto `Gal(L/F) = G ⧸ [G,G]`.

For `G` nilpotent, `B ⊔ [G,G] = ⊤` with `B` commutative forces `G` to be commutative
(`isMulCommutative_of_abelian_sup_commutator_eq_top`), contradicting `hnab`.

The bookkeeping around "the fixed field of `[G,G]` seen inside `F'`" is carried out by
`commFixedField`, `commFixedFieldMap` and `commFixedEquiv` below.
-/

open scoped Classical commutatorElement
open IntermediateField

-- `haveI` below genuinely registers typeclass instances (`IsGalois`, `IsNilpotent`); the style
-- linter, which cannot see that, asks for `have`.
set_option linter.style.haveILetI false


namespace NK.LocalCFT.NilpotentObstruction

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

/-! ### The fixed field of the commutator subgroup of `Gal(M/F)` -/

/-- The fixed field of the commutator subgroup of `Gal(M/F)`, viewed inside `M`. -/
def commFixedField (M : IntermediateField F F') : IntermediateField F ↥M :=
  IntermediateField.fixedField (commutator (↥M ≃ₐ[F] ↥M))

/-- `commFixedField M` transported into `F'` along the inclusion `↥M ↪ F'`. -/
def commFixedFieldMap (M : IntermediateField F F') : IntermediateField F F' :=
  (commFixedField M).map (IntermediateField.val M)

/-- The canonical `F`-algebra isomorphism between the two descriptions of the fixed field of the
commutator subgroup. -/
def commFixedEquiv (M : IntermediateField F F') :
    ↥(commFixedField M) ≃ₐ[F] ↥(commFixedFieldMap M) :=
  Subalgebra.equivMapOfInjective (commFixedField M).toSubalgebra (IntermediateField.val M)
    (IntermediateField.val M).injective

@[simp]
theorem commFixedEquiv_coe (M : IntermediateField F F') (x : ↥(commFixedField M)) :
    ((commFixedEquiv M x : ↥(commFixedFieldMap M)) : F') = ((x : ↥M) : F') :=
  Subalgebra.coe_equivMapOfInjective_apply _ _ _ _

/-- The commutator subgroup of `Gal(M/F)` fixes the fixed field of the commutator subgroup. -/
theorem commutator_le_fixingSubgroup_commFixedField (M : IntermediateField F F') :
    commutator (↥M ≃ₐ[F] ↥M) ≤ (commFixedField M).fixingSubgroup :=
  (IntermediateField.le_iff_le _ _).mp le_rfl

instance instIsGaloisCommFixedField (M : IntermediateField F F') [IsGalois F ↥M] :
    IsGalois F ↥(commFixedField M) :=
  IsGalois.of_fixedField_normal_subgroup (commutator (↥M ≃ₐ[F] ↥M))

instance instIsGaloisCommFixedFieldMap (M : IntermediateField F F') [IsGalois F ↥M] :
    IsGalois F ↥(commFixedFieldMap M) :=
  IsGalois.of_algEquiv (commFixedEquiv M)

instance instFiniteDimensionalCommFixedFieldMap (M : IntermediateField F F')
    [FiniteDimensional F M] : FiniteDimensional F ↥(commFixedFieldMap M) :=
  FiniteDimensional.of_surjective (commFixedEquiv M).toLinearMap
    (by simpa using (commFixedEquiv M).surjective)

/-! ### Restriction maps -/

/-- Restriction of `F`-automorphisms of `F'` to the subfield `M`. -/
def restrictGalHom (M : IntermediateField F F') [Normal F M] :
    (F' ≃ₐ[F] F') →* (↥M ≃ₐ[F] ↥M) :=
  AlgEquiv.restrictNormalHom (F := F) (K₁ := F') M

/-- Restriction of automorphisms of `M` to the fixed field of the commutator subgroup,
transported into `F'` along `commFixedEquiv`. -/
def commRestrictHom (M : IntermediateField F F') [IsGalois F ↥M] :
    (↥M ≃ₐ[F] ↥M) →* (↥(commFixedFieldMap M) ≃ₐ[F] ↥(commFixedFieldMap M)) :=
  (AlgEquiv.autCongr (commFixedEquiv M)).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M))

/-- **The kernel of the transported restriction map is precisely the commutator subgroup.** -/
theorem commRestrictHom_ker (M : IntermediateField F F') [FiniteDimensional F M]
    [IsGalois F ↥M] :
    MonoidHom.ker (commRestrictHom M) = commutator (↥M ≃ₐ[F] ↥M) := by
  have h1 : MonoidHom.ker (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M)
      (commFixedField M)) = (commFixedField M).fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker (commFixedField M)
  have h2 : (commFixedField M).fixingSubgroup = commutator (↥M ≃ₐ[F] ↥M) :=
    IntermediateField.fixingSubgroup_fixedField _
  ext g
  simp only [commRestrictHom, MonoidHom.mem_ker, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  rw [← MonoidHom.mem_ker, h1, h2]

/-- **Compatibility of the transported restriction map with restriction to `M`**:  restricting
`σ ∈ Gal(F'/F)` to `M` and then to `M^{[G,G]}` (transported into `F'`) is the same as restricting
`σ` to `commFixedFieldMap M` directly. -/
theorem commRestrictHom_comp (M : IntermediateField F F') [Normal F M] [IsGalois F ↥M]
    (σ : F' ≃ₐ[F] F') :
    commRestrictHom M (restrictGalHom M σ) =
      AlgEquiv.restrictNormalHom (F := F) (K₁ := F') (commFixedFieldMap M) σ := by
  ext y
  simp only [commRestrictHom, restrictGalHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, commFixedEquiv_coe,
    AlgEquiv.restrictNormalHom_apply]
  rw [show ((AlgEquiv.symm (commFixedEquiv M) y : ↥M) : F') = (y : F') by
    rw [← commFixedEquiv_coe M (AlgEquiv.symm (commFixedEquiv M) y), AlgEquiv.apply_symm_apply]]

/-! ### The Galois group of `M^{[G,G]}` is commutative -/

/-- The Galois group of the fixed field of the commutator subgroup (inside `M`) is commutative:
it is a quotient of `Gal(M/F) ⧸ [Gal(M/F), Gal(M/F)]`. -/
theorem commutative_gal_commFixedField (M : IntermediateField F F') [IsGalois F ↥M] :
    ∀ σ τ : ↥(commFixedField M) ≃ₐ[F] ↥(commFixedField M), σ * τ = τ * σ := by
  intro σ τ
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := ↥(commFixedField M)) (E := ↥M) τ
  obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := ↥(commFixedField M)) (E := ↥M) σ
  have hfix := commutator_le_fixingSubgroup_commFixedField (F := F) M
  have hmem : ⁅h, g⁆ ∈ (commFixedField M).fixingSubgroup :=
    hfix (Subgroup.commutator_mem_commutator (Subgroup.mem_top h) (Subgroup.mem_top g))
  have hker : (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) ⁅h, g⁆ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hmem
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at hker
  calc (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) h *
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) g
      = (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) h *
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) g *
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) h)⁻¹ *
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) g)⁻¹ *
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) g *
         (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) h) := by group
    _ = (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) g *
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥M) (commFixedField M)) h := by
          rw [hker, one_mul]

/-- The Galois group of `commFixedFieldMap M` is commutative. -/
theorem commutative_gal_commFixedFieldMap (M : IntermediateField F F') [IsGalois F ↥M] :
    ∀ σ τ : ↥(commFixedFieldMap M) ≃ₐ[F] ↥(commFixedFieldMap M), σ * τ = τ * σ := by
  have h₀ := commutative_gal_commFixedField (F := F) M
  intro σ τ
  have h1 := h₀ ((AlgEquiv.autCongr (commFixedEquiv M)).symm σ)
    ((AlgEquiv.autCongr (commFixedEquiv M)).symm τ)
  calc σ * τ = AlgEquiv.autCongr (commFixedEquiv M) ((AlgEquiv.autCongr (commFixedEquiv M)).symm σ) *
        AlgEquiv.autCongr (commFixedEquiv M) ((AlgEquiv.autCongr (commFixedEquiv M)).symm τ) := by
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    _ = AlgEquiv.autCongr (commFixedEquiv M) ((AlgEquiv.autCongr (commFixedEquiv M)).symm σ *
          (AlgEquiv.autCongr (commFixedEquiv M)).symm τ) := (map_mul _ _ _).symm
    _ = AlgEquiv.autCongr (commFixedEquiv M) ((AlgEquiv.autCongr (commFixedEquiv M)).symm τ *
          (AlgEquiv.autCongr (commFixedEquiv M)).symm σ) := by rw [h1]
    _ = AlgEquiv.autCongr (commFixedEquiv M) ((AlgEquiv.autCongr (commFixedEquiv M)).symm τ) *
        AlgEquiv.autCongr (commFixedEquiv M) ((AlgEquiv.autCongr (commFixedEquiv M)).symm σ) :=
        map_mul _ _ _
    _ = τ * σ := by rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-! ### The obstruction -/

/-- **If `F'` contains a finite normal subextension `M/F` whose Galois group is nilpotent but not
commutative, then there is no reciprocity datum `LocalReciprocityDatum F F'`.**

Indeed the image of the Artin map in `Gal(F'/F)` would be a commutative subgroup whose image `B`
in `Gal(M/F)` satisfies `B ⊔ [Gal(M/F), Gal(M/F)] = ⊤`, and a nilpotent group generated by a
commutative subgroup together with its commutator subgroup is commutative. -/
theorem not_nonempty_localReciprocityDatum_of_galoisQuotient {F : Type u} {F' : Type v}
    [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (M : IntermediateField F F') [FiniteDimensional F M] [Normal F M]
    (hnil : Group.IsNilpotent (↥M ≃ₐ[F] ↥M))
    (hnab : ∃ x y : ↥M ≃ₐ[F] ↥M, x * y ≠ y * x) :
    ¬ Nonempty (NK.LocalReciprocity.LocalReciprocityDatum F F') := by
  rintro ⟨D⟩
  haveI : IsGalois F ↥M := ⟨⟩
  haveI := hnil
  -- the Artin map of the datum, composed with the restriction `Gal(F'/F) →* Gal(M/F)`
  let φ : Fˣ →* (↥M ≃ₐ[F] ↥M) := (restrictGalHom M).comp D.artin
  -- the datum at the level `M^{[G,G]}` (which is finite and abelian over `F`)
  have hcommL := commutative_gal_commFixedFieldMap (F := F) M
  have hsurj : Function.Surjective ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F')
      (commFixedFieldMap M)).comp D.artin) := (D.isLevelIso (commFixedFieldMap M) hcommL).1
  -- hence `φ.range` surjects onto `Gal(M^{[G,G]}/F)`
  have hpsiB : φ.range.map (commRestrictHom M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha⟩ := hsurj x
    refine Subgroup.mem_map.mpr ⟨φ a, MonoidHom.mem_range.mpr ⟨a, rfl⟩, ?_⟩
    exact (commRestrictHom_comp M (D.artin a)).trans ha
  -- and since `ker (commRestrictHom M) = [G,G]`, this gives `φ.range ⊔ [G,G] = ⊤`
  have htop : φ.range ⊔ commutator (↥M ≃ₐ[F] ↥M) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : commRestrictHom M g ∈ φ.range.map (commRestrictHom M) := by
      rw [hpsiB]
      exact Subgroup.mem_top _
    obtain ⟨b, hb, hbg⟩ := Subgroup.mem_map.mp hg
    have hker : g * b⁻¹ ∈ MonoidHom.ker (commRestrictHom M) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbg, mul_inv_cancel]
    rw [commRestrictHom_ker M] at hker
    have hg' : g = (g * b⁻¹) * b := by group
    rw [hg', sup_comm]
    exact Subgroup.mul_mem_sup hker hb
  -- `φ.range` is commutative, being a quotient of the commutative group `Fˣ`
  have hBcomm : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← MonoidHom.map_mul φ a b, ← MonoidHom.map_mul φ b a, mul_comm a b]
  -- a nilpotent group generated by a commutative subgroup and its commutator subgroup is
  -- commutative, contradicting `hnab`
  have hcommG : ∀ x y : ↥M ≃ₐ[F] ↥M, x * y = y * x :=
    isMulCommutative_of_abelian_sup_commutator_eq_top φ.range hBcomm htop
  obtain ⟨x, y, hxy⟩ := hnab
  exact hxy (hcommG x y)
