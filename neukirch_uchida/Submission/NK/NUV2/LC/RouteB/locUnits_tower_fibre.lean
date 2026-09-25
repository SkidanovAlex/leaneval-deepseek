import Mathlib
import Submission.NK.NUV2.LC.LocalLevelSystem
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp
import Submission.NK.GlobalCFT.GaloisIdeles

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.NUV2.LC.RouteB

open CategoryTheory Representation NK.GlobalCFT NK.HassePrinciple

/-!
# Level independence of the localisation at the places above a fixed place

Let `F ⊆ L ⊆ M` be a tower of number fields with `L/F` and `M/F` Galois.  For a class
`b ∈ H²(Gal(L/F), Lˣ)` and two places `w₁`, `w₂` of `M` lying over the same place `w` of `L`,
the localisation of the tower image of `b` at `w₁` vanishes if and only if it vanishes at `w₂`.

The proof is the transport of the local situation along a Galois element `σ ∈ Gal(M/L)` with
`σ • w₁ = w₂` (which exists by transitivity of the Galois action on the places above `w`).  The
tower image `unitsLevelMapTower b` is fixed by the conjugation action of `Gal(M/L)` (this is the
inflation property, and uses that `σ` fixes `L` pointwise), and the localisation commutes with
conjugation; since conjugation is an isomorphism, the vanishing statements are equivalent.

## Main definitions

* `NK.NUV2.LC.RouteB.conjHom`: the conjugation endomorphism `g ↦ σ⁻¹ * (g * σ)` of `Gal(M/F)`;
* `NK.NUV2.LC.RouteB.conjStab`: its restriction to the decomposition groups,
  `Γ_{σ • w} →* Γ_w`;
* `NK.NUV2.LC.RouteB.conjUnitsCoeff`, `...conjLocalUnitsCoeff`: the induced coefficient
  isomorphisms on the global and the local units.

## Main results

* `NK.NUV2.LC.RouteB.locUnits_eq_map`, `...unitsLevelMapTower_comp_locUnits`: the localisation
  (and its composite with the tower map) as a `groupCohomology.map`;
* `NK.NUV2.LC.RouteB.conjH2_unitsLevelMapTower`: the tower image is fixed by the conjugation;
* `NK.NUV2.LC.RouteB.locUnits_tower_fibre`: the lemma of the title.
-/

section General

variable {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
  [FiniteDimensional F M] [IsGalois F M]

/-- **The conjugation endomorphism** `g ↦ σ⁻¹ * (g * σ)` of `Gal(M/F)`, the inverse of the
conjugation by `σ`; it sends the decomposition group of `σ • w` into the decomposition group of
`w` (`conjStab`). -/
noncomputable def conjHom (σ : M ≃ₐ[F] M) : (M ≃ₐ[F] M) →* (M ≃ₐ[F] M) where
  toFun g := σ⁻¹ * (g * σ)
  map_one' := by group
  map_mul' g h := by group

@[simp] theorem conjHom_apply (σ g : M ≃ₐ[F] M) : conjHom σ g = σ⁻¹ * g * σ := by
  show σ⁻¹ * (g * σ) = σ⁻¹ * g * σ
  group

/-- **The conjugation map on decomposition groups**: `g ↦ σ⁻¹ * (g * σ)` sends the decomposition
group of `σ • w` into the decomposition group of `w`. -/
noncomputable def conjStab (σ : M ≃ₐ[F] M) (w : Place M) :
    MulAction.stabilizer (M ≃ₐ[F] M) (σ • w) →* MulAction.stabilizer (M ≃ₐ[F] M) w where
  toFun g := ⟨σ⁻¹ * (g.1 * σ), by
    rw [MulAction.mem_stabilizer_iff]
    calc (σ⁻¹ * (g.1 * σ)) • w
        = σ⁻¹ • ((g.1 * σ) • w) := by rw [mul_smul]
      _ = σ⁻¹ • (g.1 • (σ • w)) := by rw [mul_smul]
      _ = σ⁻¹ • (σ • w) := by rw [MulAction.mem_stabilizer_iff.mp g.2]
      _ = (σ⁻¹ * σ) • w := by rw [mul_smul]
      _ = w := by rw [inv_mul_cancel, one_smul]⟩
  map_one' := by
    apply Subtype.ext
    show σ⁻¹ * ((1 : M ≃ₐ[F] M) * σ) = 1
    group
  map_mul' g h := by
    apply Subtype.ext
    show σ⁻¹ * ((g.1 * h.1) * σ) = (σ⁻¹ * (g.1 * σ)) * (σ⁻¹ * (h.1 * σ))
    group

@[simp] theorem conjStab_coe (σ : M ≃ₐ[F] M) (w : Place M)
    (g : MulAction.stabilizer (M ≃ₐ[F] M) (σ • w)) :
    ((conjStab σ w g : MulAction.stabilizer (M ≃ₐ[F] M) w) : M ≃ₐ[F] M) = σ⁻¹ * (g.1 * σ) := rfl

/-- **The coefficient isomorphism on the global units attached to `σ`**, as a morphism of
representations for the conjugation action: `u ↦ σ u` intertwines `ρ (σ⁻¹ g σ)` with `ρ g`. -/
noncomputable def conjUnitsCoeff (σ : M ≃ₐ[F] M) :
    Rep.res (conjHom σ) (unitsRep F M) ⟶ unitsRep F M :=
  Rep.ofHom
    { toFun := ⇑(Units.map σ.toMulEquiv.toMonoidHom).toAdditive
      map_add' := fun x y => map_add _ x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul _ z x
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        set y : Mˣ := Additive.toMul x with hy
        show Additive.ofMul (Units.map σ.toMulEquiv.toMonoidHom
              (Units.map (conjHom σ g).toMulEquiv.toMonoidHom y))
            = Additive.ofMul (Units.map g.toMulEquiv.toMonoidHom
                (Units.map σ.toMulEquiv.toMonoidHom y))
        congr 1
        apply Units.ext
        show σ ((σ⁻¹ * ((g : M ≃ₐ[F] M) * σ)) y) = (g : M ≃ₐ[F] M) (σ y)
        simp [AlgEquiv.mul_apply] }

/-- **The local automorphism intertwines the two decomposition-group actions along `σ`**: the
local isomorphism `M_w ≃+* M_{σ w}` carries the action of `conjStab σ w g` on `M_w` to the action
of `g` on `M_{σ w}`.  Both sides are continuous ring homomorphisms agreeing on the dense image of
`M`. -/
theorem localAut_conj_apply (σ : M ≃ₐ[F] M) (w : Place M)
    (g : MulAction.stabilizer (M ≃ₐ[F] M) (σ • w)) (x : Place.localField M w) :
    Place.localRingEquiv σ w (localAut w (conjStab σ w g) x)
      = localAut (σ • w) g (Place.localRingEquiv σ w x) := by
  have hdense : DenseRange (algebraMap M (Place.localField M w)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField w
  have hcont1 : Continuous (fun y : Place.localField M w =>
      Place.localRingEquiv σ w (localAut w (conjStab σ w g) y)) :=
    (NK.GlobalCFT.Galois.continuous_localRingEquiv σ w).comp
      (localAut_continuous w _)
  have hcont2 : Continuous (fun y : Place.localField M w =>
      localAut (σ • w) g (Place.localRingEquiv σ w y)) :=
    (localAut_continuous (σ • w) g).comp
      (NK.GlobalCFT.Galois.continuous_localRingEquiv σ w)
  have hfun : (fun y : Place.localField M w =>
        Place.localRingEquiv σ w (localAut w (conjStab σ w g) y)) =
      fun y => localAut (σ • w) g (Place.localRingEquiv σ w y) := by
    refine DenseRange.equalizer (f := algebraMap M (Place.localField M w)) hdense hcont1 hcont2 ?_
    funext y
    simp only [Function.comp_apply]
    rw [localAut_algebraMap, Place.localRingEquiv_algebraMap,
      Place.localRingEquiv_algebraMap, localAut_algebraMap]
    congr 1
    show σ ((σ⁻¹ * ((g : M ≃ₐ[F] M) * σ)) y) = (g : M ≃ₐ[F] M) (σ y)
    simp [AlgEquiv.mul_apply]
  exact congrFun hfun x

/-- **The coefficient isomorphism on the local units attached to `σ`**, as a morphism of
representations for the conjugation action on the decomposition groups. -/
noncomputable def conjLocalUnitsCoeff (σ : M ≃ₐ[F] M) (w : Place M) :
    Rep.res (conjStab σ w) (localUnitsRep F M w) ⟶ localUnitsRep F M (σ • w) :=
  Rep.ofHom
    { toFun := ⇑(Units.map (Place.localRingEquiv σ w).toMulEquiv.toMonoidHom).toAdditive
      map_add' := fun x y => map_add _ x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul _ z x
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        set y : (Place.localField M w)ˣ := Additive.toMul x with hy
        show Additive.ofMul (Units.map (Place.localRingEquiv σ w).toMulEquiv.toMonoidHom
              (localUnitsEquiv (K := F) w (conjStab σ w g) y))
            = Additive.ofMul (localUnitsEquiv (K := F) (σ • w) g
                (Units.map (Place.localRingEquiv σ w).toMulEquiv.toMonoidHom y))
        congr 1
        apply Units.ext
        simp only [coe_localUnitsEquiv, Units.coe_map, MulEquiv.coe_toMonoidHom]
        exact localAut_conj_apply σ w g y }

end General

section Level

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

set_option backward.isDefEq.respectTransparency false in
/-- **The localisation at `w` is the restriction to the decomposition group followed by the local
coefficient map** (the `id`-bookkeeping in the definition of `locUnits` is removed). -/
theorem locUnits_eq_map (w : Place L) :
    locUnits K L w = groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (unitsToLocalUnits K L w) 2 := by
  rw [locUnits, groupCohomology.resNatTrans_app]
  rw [← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext g
    rfl
  · rfl

end Level

section Tower

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

set_option backward.isDefEq.respectTransparency false in
/-- **The composite of the tower level map with the localisation at `w`**: the restriction to the
decomposition group of `w` of the pull-back of the units inclusion along the restriction
`Gal(M/F) →* Gal(L/F)`. -/
theorem unitsLevelMapTower_comp_locUnitsFibre (w : Place M) :
    unitsLevelMapTower ≫ locUnits F M w =
      groupCohomology.map ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)).comp
          (MulAction.stabilizer (M ≃ₐ[F] M) w).subtype)
        (CategoryTheory.CategoryStruct.comp
          ((Rep.resFunctor (MulAction.stabilizer (M ≃ₐ[F] M) w).subtype).map
            (unitsInclTowerCoeff (F := F) (L := L) (M := M)))
          (unitsToLocalUnits F M w)) 2 := by
  rw [unitsLevelMapTower, locUnits_eq_map]
  rw [← groupCohomology.map_comp]

/-- The restriction `Gal(M/F) →* Gal(L/F)` kills the elements fixing `L` pointwise. -/
theorem restrictNormalHom_eq_one_of_fixes (σ : M ≃ₐ[F] M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    AlgEquiv.restrictNormalHom (K₁ := M) (E := L) σ = 1 := by
  ext x
  have h := AlgEquiv.restrictNormal_commutes (E := L) σ x
  have h := AlgEquiv.restrictNormal_commutes (E := L) σ x
  have h2 : algebraMap L M ((AlgEquiv.restrictNormal (K₁ := M) (E := L) σ) x) =
      algebraMap L M x := by
    rw [h]
    exact hfix x
  exact (algebraMap L M).injective h2

/-- **The conjugation action of `σ` on `H²(Gal(M/F), Mˣ)`**: the map induced by the conjugation
`g ↦ σ⁻¹ g σ` of the Galois group and the coefficient isomorphism `u ↦ σ u` on the units. -/
noncomputable def conjH2 (σ : M ≃ₐ[F] M) :
    groupCohomology (unitsRep F M) 2 ⟶ groupCohomology (unitsRep F M) 2 :=
  groupCohomology.map (conjHom σ) (conjUnitsCoeff σ) 2

/-- **The conjugation action of `σ` on the local cohomology at `w`**: the map induced by the
conjugation of the decomposition groups and the local coefficient isomorphism
`M_w ≃+* M_{σ w}`. -/
noncomputable def conjLoc (σ : M ≃ₐ[F] M) (w : Place M) :
    groupCohomology (localUnitsRep F M w) 2 ⟶
      groupCohomology (localUnitsRep F M (σ • w)) 2 :=
  groupCohomology.map (conjStab σ w) (conjLocalUnitsCoeff σ w) 2

/-- The restriction `Gal(M/F) →* Gal(L/F)` is invariant under conjugation by an element fixing
`L` pointwise. -/
theorem restrictNormalHom_conjHom (σ : M ≃ₐ[F] M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)).comp (conjHom σ) =
      AlgEquiv.restrictNormalHom (K₁ := M) (E := L) := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro a
  show AlgEquiv.restrictNormalHom (K₁ := M) (E := L) (conjHom σ g) a =
    AlgEquiv.restrictNormalHom (K₁ := M) (E := L) g a
  rw [conjHom_apply, map_mul, map_mul, map_inv,
    restrictNormalHom_eq_one_of_fixes σ hfix]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The units inclusion `Lˣ → Mˣ` is invariant under the conjugation coefficient map, since `σ`
fixes `L` pointwise. -/
theorem conjUnitsCoeff_comp_unitsInclTowerCoeff (σ : M ≃ₐ[F] M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    (Rep.Hom.hom ((Rep.resFunctor (conjHom σ)).map
          (unitsInclTowerCoeff (F := F) (L := L) (M := M)) ≫ conjUnitsCoeff σ)).toLinearMap =
      (Rep.Hom.hom (unitsInclTowerCoeff (F := F) (L := L) (M := M))).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
  set y : Lˣ := Additive.toMul x with hy
  show Additive.ofMul (Units.map σ.toMulEquiv.toMonoidHom
        (Units.map (algebraMap L M).toMonoidHom y)) =
      Additive.ofMul (Units.map (algebraMap L M).toMonoidHom y)
  congr 1
  apply Units.ext
  simp only [Units.coe_map, MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe]
  exact hfix y

set_option backward.isDefEq.respectTransparency false in
/-- **The tower image of a class is fixed by the conjugation action** of an element `σ` which
fixes `L` pointwise: this is the inflation property of `unitsLevelMapTower`. -/
theorem conjH2_unitsLevelMapTower (σ : M ≃ₐ[F] M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x)
    (b : groupCohomology (unitsRep F L) 2) :
    (conjH2 (F := F) (M := M) σ) ((unitsLevelMapTower (F := F) (L := L) (M := M)) b) =
      (unitsLevelMapTower (F := F) (L := L) (M := M)) b := by
  have key : (unitsLevelMapTower (F := F) (L := L) (M := M)) ≫ conjH2 (F := F) (M := M) σ =
      unitsLevelMapTower (F := F) (L := L) (M := M) := by
    rw [unitsLevelMapTower, conjH2]
    rw [← groupCohomology.map_comp]
    refine groupCohomology.map_congr
      (restrictNormalHom_conjHom (F := F) (L := L) (M := M) σ hfix) ?_ 2
    exact conjUnitsCoeff_comp_unitsInclTowerCoeff (F := F) (L := L) (M := M) σ hfix
  simpa only [CategoryTheory.comp_apply] using congrArg (fun f => f.hom b) key

/-- The restriction map on the decomposition groups is invariant under the conjugation: for `g` in
the decomposition group of `σ • w`, the restrictions of `g` and of `σ⁻¹ g σ` to `L` agree. -/
theorem restrictNormalHom_conjStab (σ : M ≃ₐ[F] M) (w : Place M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)).comp
        (MulAction.stabilizer (M ≃ₐ[F] M) (σ • w)).subtype =
      ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)).comp
        (MulAction.stabilizer (M ≃ₐ[F] M) w).subtype).comp (conjStab σ w) := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro a
  show AlgEquiv.restrictNormalHom (K₁ := M) (E := L) (g : M ≃ₐ[F] M) a =
    AlgEquiv.restrictNormalHom (K₁ := M) (E := L)
      ((conjStab σ w g : MulAction.stabilizer (M ≃ₐ[F] M) w) : M ≃ₐ[F] M) a
  rw [conjStab_coe, map_mul, map_mul, map_inv,
    restrictNormalHom_eq_one_of_fixes σ hfix]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The local coefficient isomorphism is compatible with the coefficient maps of the tower: on the
global units, the localisation at `σ • w` is the conjugation of the localisation at `w`, because
`σ` fixes `L` pointwise. -/
theorem conjLocalUnitsCoeff_comp (σ : M ≃ₐ[F] M) (w : Place M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    (Rep.Hom.hom (((Rep.resFunctor (MulAction.stabilizer (M ≃ₐ[F] M) (σ • w)).subtype).map
        (unitsInclTowerCoeff (F := F) (L := L) (M := M)) ≫ unitsToLocalUnits F M (σ • w)))).toLinearMap =
      (Rep.Hom.hom (((Rep.resFunctor (conjStab σ w)).map
            ((Rep.resFunctor (MulAction.stabilizer (M ≃ₐ[F] M) w).subtype).map
              (unitsInclTowerCoeff (F := F) (L := L) (M := M)) ≫ unitsToLocalUnits F M w) ≫
          conjLocalUnitsCoeff σ w))).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
  set y : Lˣ := Additive.toMul x with hy
  show Additive.ofMul (Units.map (algebraMap M (Place.localField M (σ • w))).toMonoidHom
        (Units.map (algebraMap L M).toMonoidHom y)) =
      Additive.ofMul (Units.map (Place.localRingEquiv σ w).toMulEquiv.toMonoidHom
        (Units.map (algebraMap M (Place.localField M w)).toMonoidHom
          (Units.map (algebraMap L M).toMonoidHom y)))
  congr 1
  apply Units.ext
  show algebraMap M (Place.localField M (σ • w)) (algebraMap L M (y : L)) =
    Place.localRingEquiv σ w (algebraMap M (Place.localField M w) (algebraMap L M (y : L)))
  rw [Place.localRingEquiv_algebraMap, hfix (y : L)]

set_option backward.isDefEq.respectTransparency false in
/-- **The localisation commutes with the conjugation action of an element `σ` fixing `L`**. -/
theorem locUnits_conj (σ : M ≃ₐ[F] M) (w : Place M)
    (hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    (unitsLevelMapTower (F := F) (L := L) (M := M)) ≫ locUnits F M (σ • w) =
      ((unitsLevelMapTower (F := F) (L := L) (M := M)) ≫ locUnits F M w) ≫
        conjLoc (F := F) (M := M) σ w := by
  rw [unitsLevelMapTower_comp_locUnitsFibre (F := F) (L := L) (M := M) (σ • w),
    unitsLevelMapTower_comp_locUnitsFibre (F := F) (L := L) (M := M) w, conjLoc]
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ 2
  · exact restrictNormalHom_conjStab (F := F) (L := L) (M := M) σ w hfix
  · exact conjLocalUnitsCoeff_comp (F := F) (L := L) (M := M) σ w hfix

/-- **The conjugation isomorphism of decomposition groups** `Γ_w ≃* Γ_{σ w}`. -/
noncomputable def conjStabEquiv (σ : M ≃ₐ[F] M) (w : Place M) :
    MulAction.stabilizer (M ≃ₐ[F] M) w ≃* MulAction.stabilizer (M ≃ₐ[F] M) (σ • w) where
  toFun g := ⟨σ * (g.1 * σ⁻¹), by
    rw [MulAction.mem_stabilizer_iff]
    calc (σ * (g.1 * σ⁻¹)) • (σ • w)
        = σ • ((g.1 * σ⁻¹) • (σ • w)) := by rw [mul_smul]
      _ = σ • (g.1 • (σ⁻¹ • (σ • w))) := by rw [mul_smul]
      _ = σ • (g.1 • w) := by rw [inv_smul_smul]
      _ = σ • w := by rw [MulAction.mem_stabilizer_iff.mp g.2]⟩
  invFun := conjStab σ w
  left_inv g := by
    apply Subtype.ext
    show σ⁻¹ * ((σ * (g.1 * σ⁻¹)) * σ) = g.1
    group
  right_inv g := by
    apply Subtype.ext
    show σ * ((σ⁻¹ * (g.1 * σ)) * σ⁻¹) = g.1
    group
  map_mul' g h := by
    apply Subtype.ext
    show σ * ((g.1 * h.1) * σ⁻¹) = (σ * (g.1 * σ⁻¹)) * (σ * (h.1 * σ⁻¹))
    group

@[simp] theorem conjStabEquiv_coe (σ : M ≃ₐ[F] M) (w : Place M)
    (g : MulAction.stabilizer (M ≃ₐ[F] M) w) :
    ((conjStabEquiv σ w g : MulAction.stabilizer (M ≃ₐ[F] M) (σ • w)) : M ≃ₐ[F] M) =
      σ * (g.1 * σ⁻¹) := rfl

/-- **The density form of the equivariance of the local isomorphism**: the isomorphism
`M_w ≃+* M_{σ w}` intertwines the automorphism of `M_w` attached to `g` with the automorphism of
`M_{σ w}` attached to the conjugate of `g`. -/
theorem localRingEquiv_localAut_of_conj (σ : M ≃ₐ[F] M) (w : Place M)
    (g : MulAction.stabilizer (M ≃ₐ[F] M) w) (x : Place.localField M w) :
    Place.localRingEquiv σ w (localAut w g x) =
      localAut (σ • w) (conjStabEquiv σ w g) (Place.localRingEquiv σ w x) := by
  have hdense : DenseRange (algebraMap M (Place.localField M w)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField w
  have hcont1 :
      Continuous (fun y : Place.localField M w => Place.localRingEquiv σ w (localAut w g y)) :=
    (NK.GlobalCFT.Galois.continuous_localRingEquiv σ w).comp (localAut_continuous w g)
  have hcont2 : Continuous (fun y : Place.localField M w =>
      localAut (σ • w) (conjStabEquiv σ w g) (Place.localRingEquiv σ w y)) :=
    (localAut_continuous (σ • w) (conjStabEquiv σ w g)).comp
      (NK.GlobalCFT.Galois.continuous_localRingEquiv σ w)
  have hfun : (fun y : Place.localField M w =>
        Place.localRingEquiv σ w (localAut w g y)) =
      fun y => localAut (σ • w) (conjStabEquiv σ w g) (Place.localRingEquiv σ w y) := by
    refine DenseRange.equalizer (f := algebraMap M (Place.localField M w)) hdense hcont1 hcont2 ?_
    funext y
    simp only [Function.comp_apply]
    rw [localAut_algebraMap, Place.localRingEquiv_algebraMap,
      Place.localRingEquiv_algebraMap, localAut_algebraMap]
    congr 1
    show σ ((g : M ≃ₐ[F] M) y) = (σ * ((g : M ≃ₐ[F] M) * σ⁻¹)) (σ y)
    simp [AlgEquiv.mul_apply]
  exact congrFun hfun x

/-- **The local coefficient isomorphism attached to `σ` as a linear equivalence** of the local
unit groups (with the `CoeffInt`-module structure). -/
noncomputable def conjLocalUnitsLinearEquiv (σ : M ≃ₐ[F] M) (w : Place M) :
    Additive ((Place.localField M w)ˣ) ≃ₗ[NK.HassePrinciple.CoeffInt]
      Additive ((Place.localField M (σ • w))ˣ) :=
  ((Units.mapEquiv (Place.localRingEquiv σ w).toMulEquiv).toAdditive).toLinearEquiv
    (fun c x => map_zsmul _ c.down x)

set_option backward.isDefEq.respectTransparency false in
/-- **The equivariance of the local coefficient isomorphism** under the conjugation isomorphism of
decomposition groups. -/
theorem conjLocalUnitsLinearEquiv_intertwining (σ : M ≃ₐ[F] M) (w : Place M)
    (g : MulAction.stabilizer (M ≃ₐ[F] M) w) (x : (Additive ((Place.localField M w)ˣ))) :
    conjLocalUnitsLinearEquiv (F := F) (M := M) σ w
        ((localUnitsRep F M w).ρ g x) =
      (localUnitsRep F M (σ • w)).ρ (conjStabEquiv σ w g)
        (conjLocalUnitsLinearEquiv (F := F) (M := M) σ w x) := by
  set y : (Place.localField M w)ˣ := Additive.toMul x with hy
  show Additive.ofMul ((Units.mapEquiv (Place.localRingEquiv σ w).toMulEquiv)
        (localUnitsEquiv (K := F) w g y)) =
      Additive.ofMul (localUnitsEquiv (K := F) (σ • w) (conjStabEquiv σ w g)
        ((Units.mapEquiv (Place.localRingEquiv σ w).toMulEquiv) y))
  congr 1
  apply Units.ext
  simp only [coe_localUnitsEquiv, Units.coe_mapEquiv]
  exact localRingEquiv_localAut_of_conj σ w g y

/-- **The conjugation isomorphism of the local cohomology groups** `H²(Γ_w, M_wˣ) ≅
H²(Γ_{σ w}, M_{σ w}ˣ)` induced by the conjugation isomorphism of the decomposition groups and the
local coefficient isomorphism `M_w ≃+* M_{σ w}`. -/
noncomputable def conjLocIso (σ : M ≃ₐ[F] M) (w : Place M) :
    groupCohomology (localUnitsRep F M w) 2 ≅
      groupCohomology (localUnitsRep F M (σ • w)) 2 :=
  groupCohomology.mapIso (A := localUnitsRep F M (σ • w)) (B := localUnitsRep F M w)
    (conjStabEquiv σ w) (conjLocalUnitsLinearEquiv (F := F) (M := M) σ w)
    (fun g => by
      apply LinearMap.ext
      intro x
      set y : (Place.localField M w)ˣ := Additive.toMul x with hy
      show Additive.ofMul ((Units.mapEquiv (Place.localRingEquiv σ w).toMulEquiv)
            (localUnitsEquiv (K := F) w g y)) =
          Additive.ofMul (localUnitsEquiv (K := F) (σ • w) (conjStabEquiv σ w g)
            ((Units.mapEquiv (Place.localRingEquiv σ w).toMulEquiv) y))
      congr 1
      apply Units.ext
      simp only [coe_localUnitsEquiv, Units.coe_mapEquiv]
      exact localRingEquiv_localAut_of_conj σ w g y) 2

set_option backward.isDefEq.respectTransparency false in
/-- **The localisation commutes with conjugation, as an isomorphism of the cohomology groups.**
`conjLoc` is the `hom` of the isomorphism induced by the conjugation of the decomposition groups
and the local coefficient isomorphism. -/
theorem conjLoc_eq_mapIso (σ : M ≃ₐ[F] M) (w : Place M) :
    conjLoc (F := F) (M := M) σ w = (conjLocIso (F := F) (M := M) σ w).hom := by
  show groupCohomology.map (conjStab σ w) (conjLocalUnitsCoeff (F := F) (M := M) σ w) 2 = _
  refine groupCohomology.map_congr ?_ ?_ 2
  · exact MonoidHom.ext fun g => rfl
  · apply LinearMap.ext
    intro x
    set y : (Place.localField M w)ˣ := Additive.toMul x with hy
    show Additive.ofMul (Units.map (Place.localRingEquiv σ w).toMulEquiv.toMonoidHom y) =
      Additive.ofMul ((Units.mapEquiv (Place.localRingEquiv σ w).toMulEquiv) y)
    rfl

/-- **The conjugated localisation detects zero**: a class of `H²(Γ_w, M_wˣ)` is killed by the
conjugation isomorphism if and only if it is zero. -/
theorem conjLoc_eq_zero_iff (σ : M ≃ₐ[F] M) (w : Place M)
    (y : groupCohomology (localUnitsRep F M w) 2) :
    (conjLoc (F := F) (M := M) σ w).hom y = 0 ↔ y = 0 := by
  let Φ := conjLocIso (F := F) (M := M) σ w
  have hhom : conjLoc (F := F) (M := M) σ w = Φ.hom := conjLoc_eq_mapIso (F := F) (M := M) σ w
  have hcomp0 : conjLoc (F := F) (M := M) σ w ≫ Φ.inv =
      𝟙 (groupCohomology (localUnitsRep F M w) 2) := by
    rw [hhom]
    exact Φ.hom_inv_id
  constructor
  · intro hy
    have h := congrArg (fun (f : groupCohomology (localUnitsRep F M w) 2 ⟶
        groupCohomology (localUnitsRep F M w) 2) => f.hom y) hcomp0
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, hy, map_zero] at h
    exact h.symm
  · intro hy
    rw [hy, map_zero]

end Tower

section Main

theorem locUnits_tower_fibre {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]
    (b : groupCohomology (NK.HassePrinciple.unitsRep F L) 2)
    {w : NK.GlobalCFT.Place L} {w₁ w₂ : NK.GlobalCFT.Place M}
    (h₁ : NK.GlobalCFT.Place.LiesOver w₁ w) (h₂ : NK.GlobalCFT.Place.LiesOver w₂ w) :
    (NK.HassePrinciple.locUnits F M w₁).hom
        ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) b) = 0 ↔
      (NK.HassePrinciple.locUnits F M w₂).hom
        ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) b) = 0 := by
  haveI : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  -- a Galois element of `Gal(M/L)` carrying `w₁` to `w₂`
  obtain ⟨σ₀, hσ₀⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
    (K := L) (L := M) h₁ h₂
  set σ : M ≃ₐ[F] M := AlgEquiv.restrictScalars F σ₀ with hσdef
  have hσ : σ • w₁ = w₂ := by
    show (AlgEquiv.restrictScalars F σ₀) • w₁ = w₂
    rw [show (AlgEquiv.restrictScalars F σ₀) • w₁ = σ₀ • w₁ from rfl]
    exact hσ₀
  have hfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := fun x =>
    AlgEquiv.commutes σ₀ x
  subst hσ
  -- the localisation at `σ • w₁` of the tower image is the conjugation of the one at `w₁`
  have hloc := congrArg (fun f => f.hom b)
    (locUnits_conj (F := F) (L := L) (M := M) σ w₁ hfix)
  simp only [CategoryTheory.comp_apply] at hloc
  rw [hloc, conjLoc_eq_zero_iff]

end Main

end NK.NUV2.LC.RouteB
