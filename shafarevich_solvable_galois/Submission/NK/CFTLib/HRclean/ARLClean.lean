import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.HR.TransferAux.Setup
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

/-!
# CLEAN COPY (agent H-): the level-change (inflation) infrastructure, renamed

Merged copies of `Submission/Work/NUV2/ARL/HR/TransferSupport.lean` and
`Submission/Work/NUV2/ARL/HR/exists_cycClassOf_of_res_eq_zero.lean`, with all declarations moved
into the fresh namespace `NK.CFTLib.HRclean.ARL` (the originals are reachable from the deliverable
through `badSet_not_singleton`, so keeping the original names would collide in any file importing
both).  Statements and proofs are unchanged.  See `README.md` in this directory.
-/
namespace NK.CFTLib.HRclean.ARL




variable {K L E : Type} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E] [Algebra L E]
  [IsScalarTower K L E]

/-- The image of `L` in `E`, as an intermediate field of `E`. -/
noncomputable def imageField : IntermediateField K E :=
  (⊤ : IntermediateField K L).map (IsScalarTower.toAlgHom K L E)

/-- The `K`-algebra map `L → ↥(imageField)` is bijective, hence an isomorphism of `K`-algebras. -/
noncomputable def imageEquiv : L ≃ₐ[K] ↥(imageField (K := K) (L := L) (E := E)) :=
  AlgEquiv.ofBijective
    { toFun := fun y => ⟨algebraMap L E y, by
        change (IsScalarTower.toAlgHom K L E) y ∈
          (⊤ : IntermediateField K L).map (IsScalarTower.toAlgHom K L E)
        rw [IntermediateField.map_mem_map]; trivial⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp
      commutes' := by intro k; ext; simp [IsScalarTower.algebraMap_apply K L E] }
    (by
      constructor
      · intro x y h
        exact (algebraMap L E).injective (congrArg Subtype.val h)
      · intro z
        have hz : (z : E) ∈ (⊤ : IntermediateField K L).map (IsScalarTower.toAlgHom K L E) := z.2
        obtain ⟨y, -, hy⟩ := (IntermediateField.mem_map (⊤ : IntermediateField K L)
          (f := IsScalarTower.toAlgHom K L E)).mp hz
        exact ⟨y, Subtype.ext hy⟩)

@[simp]
lemma imageEquiv_apply_coe (y : L) :
    ((imageEquiv (K := K) (L := L) (E := E) y : ↥(imageField (K:=K) (L:=L) (E:=E))) : E)
      = algebraMap L E y := rfl

variable [IsGalois K L]

instance imageField_isGalois : IsGalois K ↥(imageField (K := K) (L := L) (E := E)) :=
  IsGalois.of_algEquiv (imageEquiv (K := K) (L := L) (E := E))

/-- **The restriction map** `Gal(E/K) →* Gal(L/K)`: an automorphism of `E` over `K` is restricted to
the image of `L` in `E` and transported back to `L` along the canonical isomorphism. -/
noncomputable def restrictHom : Gal(E/K) →* Gal(L/K) where
  toFun σ := (imageEquiv (K := K) (L := L) (E := E)).trans
    (((AlgEquiv.restrictNormalHom ↥(imageField (K := K) (L := L) (E := E))) σ).trans
      (imageEquiv (K := K) (L := L) (E := E)).symm)
  map_one' := by
    ext y
    show (imageEquiv (K := K) (L := L) (E := E)).symm
      ((AlgEquiv.restrictNormalHom ↥(imageField (K := K) (L := L) (E := E)) 1)
        ((imageEquiv (K := K) (L := L) (E := E)) y)) = y
    rw [map_one]
    simp
  map_mul' := by
    intro σ τ
    ext y
    show (imageEquiv (K := K) (L := L) (E := E)).symm
      ((AlgEquiv.restrictNormalHom ↥(imageField (K := K) (L := L) (E := E)) (σ * τ))
        ((imageEquiv (K := K) (L := L) (E := E)) y)) = _
    rw [map_mul]
    simp only [AlgEquiv.mul_apply, AlgEquiv.trans_apply]
    rw [AlgEquiv.apply_symm_apply]

/-- **The characteristic property of the restriction map**: restricting `σ` to `L` and sending the
result into `E` is the same as applying `σ` to the image of `L`. -/
lemma restrictHom_apply_coe (σ : Gal(E/K)) (y : L) :
    algebraMap L E (restrictHom (K := K) (L := L) (E := E) σ y) = σ (algebraMap L E y) := by
  have h2 : (imageEquiv (K := K) (L := L) (E := E))
        (restrictHom (K := K) (L := L) (E := E) σ y)
      = (AlgEquiv.restrictNormalHom ↥(imageField (K := K) (L := L) (E := E)) σ)
          ((imageEquiv (K := K) (L := L) (E := E)) y) := by
    show (imageEquiv (K := K) (L := L) (E := E))
        ((imageEquiv (K := K) (L := L) (E := E)).symm
          ((AlgEquiv.restrictNormalHom ↥(imageField (K := K) (L := L) (E := E)) σ)
            ((imageEquiv (K := K) (L := L) (E := E)) y))) = _
    rw [AlgEquiv.apply_symm_apply]
  have h3 := AlgEquiv.restrictNormal_commutes σ ↥(imageField (K := K) (L := L) (E := E))
    ((imageEquiv (K := K) (L := L) (E := E)) y)
  calc algebraMap L E (restrictHom (K := K) (L := L) (E := E) σ y)
      = (((imageEquiv (K := K) (L := L) (E := E))
          (restrictHom (K := K) (L := L) (E := E) σ y) :
            ↥(imageField (K := K) (L := L) (E := E))) : E) := rfl
    _ = ((((AlgEquiv.restrictNormalHom ↥(imageField (K := K) (L := L) (E := E)) σ)
          ((imageEquiv (K := K) (L := L) (E := E)) y) :
            ↥(imageField (K := K) (L := L) (E := E)))) : E) := by rw [h2]
    _ = σ ((((imageEquiv (K := K) (L := L) (E := E)) y) :
            ↥(imageField (K := K) (L := L) (E := E))) : E) := h3
    _ = σ (algebraMap L E y) := by rfl

/-! ## The coefficient map and the inflation -/

/-- The unit map `Lˣ → Eˣ` as a morphism of representations along the restriction
`Gal(E/K) →* Gal(L/K)`; equivariance is `restrictHom_apply_coe`. -/
noncomputable def unitsInclRep :
    Rep.res (restrictHom (K := K) (L := L) (E := E)) (NK.HassePrinciple.unitsRep K L) ⟶
      NK.HassePrinciple.unitsRep K E :=
  Rep.ofHom
    { toFun := ⇑(Units.map (algebraMap L E).toMonoidHom).toAdditive
      map_add' := fun x y => map_add (Units.map (algebraMap L E).toMonoidHom).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (Units.map (algebraMap L E).toMonoidHom).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (Units.map (algebraMap L E).toMonoidHom
            (Units.map (restrictHom (K := K) (L := L) (E := E) σ).toMonoidHom
              (Additive.toMul x : Lˣ)))
          = Additive.ofMul (Units.map σ.toMonoidHom
              (Units.map (algebraMap L E).toMonoidHom (Additive.toMul x : Lˣ)))
        congr 1
        refine Units.ext ?_
        simp only [Units.coe_map]
        exact restrictHom_apply_coe σ ((Additive.toMul x : Lˣ) : L) }

/-- **The inflation** `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)` along the restriction map. -/
noncomputable def inflation :
    groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
      groupCohomology (NK.HassePrinciple.unitsRep K E) 2 :=
  groupCohomology.map (restrictHom (K := K) (L := L) (E := E))
    (unitsInclRep (K := K) (L := L) (E := E)) 2




/-! ## The restriction `Gal(E/M) →* Gal(E/K)` and the composite restriction -/

section Composite

variable {K L M E : Type} [Field K] [Field M] [Field E] [Algebra K M] [Algebra K E]
  [Algebra M E] [IsScalarTower K M E]

/-- The inclusion `Gal(E/M) →* Gal(E/K)` (restriction of scalars). -/
noncomputable def inclMK : Gal(E/M) →* Gal(E/K) where
  toFun σ := AlgEquiv.restrictScalars K σ
  map_one' := by ext x; rfl
  map_mul' := by intro σ τ; ext x; rfl

@[simp]
lemma inclMK_apply (σ : Gal(E/M)) : (inclMK (K := K) (M := M) (E := E) σ : E → E) = σ := rfl

end Composite

section CompositeRestrict

variable {K L M E : Type} [Field K] [Field L] [Field M] [Field E] [Algebra K L] [Algebra K M]
  [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
  [IsGalois K L]

/-- The composite restriction `Gal(E/M) →* Gal(L/K)`. -/
noncomputable def rhoRestrict : Gal(E/M) →* Gal(L/K) :=
  (restrictHom (K := K) (L := L) (E := E)).comp (inclMK (K := K) (M := M) (E := E))

lemma rhoRestrict_apply_coe (σ : Gal(E/M)) (y : L) :
    algebraMap L E (rhoRestrict (K := K) (L := L) (M := M) (E := E) σ y)
      = σ (algebraMap L E y) := by
  show algebraMap L E (restrictHom (K := K) (L := L) (E := E)
    (AlgEquiv.restrictScalars K σ) y) = _
  rw [restrictHom_apply_coe]
  rfl

/-- The unit map `Lˣ → Eˣ` as a morphism of representations along the composite restriction, where
the target `Eˣ` carries the `Gal(E/M)`-action. -/
noncomputable def unitsInclRepM :
    Rep.res (rhoRestrict (K := K) (L := L) (M := M) (E := E))
        (NK.HassePrinciple.unitsRep K L) ⟶
      NK.HassePrinciple.unitsRep M E :=
  Rep.ofHom
    { toFun := ⇑(Units.map (algebraMap L E).toMonoidHom).toAdditive
      map_add' := fun x y => map_add (Units.map (algebraMap L E).toMonoidHom).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (Units.map (algebraMap L E).toMonoidHom).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (Units.map (algebraMap L E).toMonoidHom
            (Units.map (rhoRestrict (K := K) (L := L) (M := M) (E := E) σ).toMonoidHom
              (Additive.toMul x : Lˣ)))
          = Additive.ofMul (Units.map σ.toMonoidHom
              (Units.map (algebraMap L E).toMonoidHom (Additive.toMul x : Lˣ)))
        congr 1
        refine Units.ext ?_
        simp only [Units.coe_map]
        exact rhoRestrict_apply_coe σ ((Additive.toMul x : Lˣ) : L) }

end CompositeRestrict

section ResToGal

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E]

/-- **The restriction `H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)`** along the inclusion of the subgroup
`Gal(E/M) ↪ Gal(E/K)`, in the `unitsRep` vocabulary. -/
noncomputable def resToGal :
    groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
      groupCohomology (NK.HassePrinciple.unitsRep M E) 2 :=
  (groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
    (inclMK (K := K) (M := M) (E := E)) 2).app (NK.HassePrinciple.unitsRep K E)

end ResToGal




variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [FiniteDimensional K M]
  [FiniteDimensional K E] [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-- The coefficient representation `Eˣ` of `Gal(E/K)`. -/
noncomputable abbrev unitsA : Rep NK.HassePrinciple.CoeffInt (Gal(E/K)) :=
  NK.HassePrinciple.unitsRep K E

/-- The kernel of the restriction `Gal(E/K) →* Gal(M/K)`, i.e. the Galois group of `E` over the
image of `M`. -/
noncomputable abbrev rn : Subgroup (Gal(E/K)) := NK.CFTLib.HR.TransferAux.rN K M E

/-! ## The restriction map is Mathlib's `AlgEquiv.restrictNormalHom` -/

/-- The restriction `Gal(E/K) →* Gal(M/K)` of `NK.NUV2.ARL.HR.TransferSupport` is Mathlib's
`AlgEquiv.restrictNormalHom` for the tower `K ⊆ M ⊆ E`. -/
theorem restrictHom_eq_restrictNormalHom :
    NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := M) (E := E)
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := M) := by
  ext σ x
  apply (algebraMap M E).injective
  rw [restrictHom_apply_coe]
  exact (AlgEquiv.restrictNormal_commutes (F := K) (K₁ := E) (K₂ := E) σ M x).symm

/-- Membership in `rN K M E`, characterised by fixing `M` pointwise. -/
theorem mem_rn_iff (σ : Gal(E/K)) :
    σ ∈ rn (K := K) (M := M) (E := E) ↔
      ∀ m : M, σ (algebraMap M E m) = algebraMap M E m := by
  rw [rn, NK.CFTLib.HR.TransferAux.rN, MonoidHom.mem_ker]
  have key : ∀ τ : Gal(M/K), τ = 1 ↔ ∀ m : M, τ m = m := by
    intro τ; constructor
    · intro h m; rw [h]; rfl
    · intro h; ext m; exact h m
  rw [key]
  constructor
  · intro h m
    have h1 := AlgEquiv.restrictNormal_commutes (F := K) (K₁ := E) (K₂ := E) σ M m
    have h2 : (σ.restrictNormal M) m = m := h m
    rw [h2] at h1
    exact h1.symm
  · intro h m
    apply (algebraMap M E).injective
    have h1 := AlgEquiv.restrictNormal_commutes (F := K) (K₁ := E) (K₂ := E) σ M m
    rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := M)) σ
      = σ.restrictNormal M from rfl]
    rw [h1]
    exact h m

/-! ## The canonical isomorphism `Gal(E/M) ≃* rN K M E` -/

/-- The canonical isomorphism between `Gal(E/M)` and the kernel `rN K M E` of the restriction,
sending `τ` to its image in `Gal(E/K)`. -/
noncomputable def galEquivRhn : Gal(E/M) ≃* rn (K := K) (M := M) (E := E) where
  toFun τ := ⟨NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E) τ, by
    rw [mem_rn_iff]; intro m; exact τ.commutes m⟩
  invFun s := AlgEquiv.ofRingEquiv (f := (s.1).toRingEquiv)
    (fun m => (mem_rn_iff (s.1)).mp s.2 m)
  left_inv τ := AlgEquiv.ext fun x => rfl
  right_inv s := Subtype.ext (AlgEquiv.ext fun x => rfl)
  map_mul' a b := Subtype.ext (map_mul _ a b)

@[simp]
theorem galEquivRhn_apply_coe (τ : Gal(E/M)) :
    ((galEquivRhn (K := K) (M := M) (E := E) τ : rn (K := K) (M := M) (E := E)) : Gal(E/K))
      = NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E) τ := rfl

theorem rn_subtype_comp_galEquivRhn :
    (rn (K := K) (M := M) (E := E)).subtype.comp (galEquivRhn (K := K) (M := M) (E := E))
      = NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E) := by
  ext τ; rfl

/-! ## Hilbert 90 for the restricted units -/

/-- **Hilbert 90 for the kernel subgroup**: `H¹(rN K M E, Eˣ) = 0`, since `rN K M E ≅ Gal(E/M)`
and `H¹(Gal(E/M), Eˣ) = 0`. -/
theorem subsingleton_H1_res_rn :
    Subsingleton (groupCohomology
      (Rep.res (rn (K := K) (M := M) (E := E)).subtype (unitsA (K := K) (E := E))) 1) := by
  haveI hME : Subsingleton (groupCohomology (NK.HassePrinciple.unitsRep M E) 1) :=
    NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep (K := M) (L := E)
  have h₁ : groupCohomology
      (Rep.res (galEquivRhn (K := K) (M := M) (E := E)).symm
        (NK.HassePrinciple.unitsRep M E)) 1 ≅
      groupCohomology (NK.HassePrinciple.unitsRep M E) 1 :=
    groupCohomology.mapIso (galEquivRhn (K := K) (M := M) (E := E)).symm
      (LinearEquiv.refl NK.HassePrinciple.CoeffInt (NK.HassePrinciple.unitsRep M E).V)
      (by intro g; rfl) 1
  exact ⟨fun a b => (Iso.toLinearEquiv h₁).injective (Subsingleton.elim _ _)⟩


/-! ## The restriction side -/



end NK.CFTLib.HRclean.ARL
