import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Degree `0`: group cohomology is `Ext`-cohomology, naturally in the coefficients

For every group `G` and every `A : Rep Coeff G` there is an additive isomorphism
`H⁰(G, A) ≃+ extH A 0 = Ext⁰_G(ℤ, A)`, natural in `A` with respect to the map induced by a
morphism of representations `φ : A ⟶ B` on the one hand (`groupCohomology.map (id) φ 0`) and
post-composition with `Ext.mk₀ φ` on the other.

Both sides are the invariants `A.ρ.invariants`:
* `groupCohomology.H0Iso A : H⁰(G,A) ≅ A.ρ.invariants`, natural in `A` by
  `groupCohomology.map_id_comp_H0Iso_hom` together with `Rep.invariantsFunctor`;
* `extH A 0 ≃ (unitRep G ⟶ A) ≃ A.ρ.invariants`, where the last map is evaluation at `1`.

## Implementation note

The coefficient ring is `Coeff = ULift ℤ`; its generic `ULift.module` instance competes with the
module structures that occur in Mathlib's `ModuleCat`-based group cohomology.  We remove it locally
(as in `Submission/NK/HassePrinciple/injective_h2_units_of_subsingleton_h1_classGroupRep.lean`) so
that the `Rep`-instances are used consistently.
-/

open CategoryTheory Representation

attribute [local instance 10000] Rep.hV1 Rep.hV2

attribute [-instance] ULift.module

noncomputable section

namespace Work.SSGRoute

variable {G : Type} [Group G]

/-! ## The bijection `(unitRep G ⟶ A) ≃ A.ρ.invariants` -/

/-- The class `f : unitRep G ⟶ A` is determined by its value `f 1`, which is `G`-invariant. -/
def eZeroToInv (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (f : SSGRoute.PTExt.unitRep G ⟶ A) : ↥A.ρ.invariants :=
  ⟨f.hom (1 : SSGRoute.PTExt.Coeff), fun g => by
    rw [← Rep.hom_comm_apply f g (1 : SSGRoute.PTExt.Coeff)]
    rfl⟩

/-- A `G`-invariant element `x` of `A` gives a morphism `unitRep G ⟶ A`, `c ↦ c • x`. -/
def eZeroOfInv (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (x : ↥A.ρ.invariants) : SSGRoute.PTExt.unitRep G ⟶ A :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (SSGRoute.PTExt.unitRep G).ρ A.ρ
    (LinearMap.toSpanSingleton SSGRoute.PTExt.Coeff ↥A (x : A))
    (fun g v => by
      rw [show ((SSGRoute.PTExt.unitRep G).ρ g) v = v from rfl]
      have hf : (LinearMap.toSpanSingleton SSGRoute.PTExt.Coeff ↥A (x : A)) =
          A.ρ g ∘ₗ (LinearMap.toSpanSingleton SSGRoute.PTExt.Coeff ↥A (x : A)) := by
        apply LinearMap.ext_ring
        rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply_one]
        exact (x.2 g).symm
      exact congrFun (congrArg DFunLike.coe hf) v))

@[simp]
lemma eZeroOfInv_hom_apply (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (x : ↥A.ρ.invariants) (c : SSGRoute.PTExt.Coeff) :
    (Rep.Hom.hom (eZeroOfInv G A x)).toLinearMap c
      = (LinearMap.toSpanSingleton SSGRoute.PTExt.Coeff ↥A (x : A)) c := rfl

lemma eZeroToInv_eZeroOfInv (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (x : ↥A.ρ.invariants) : eZeroToInv G A (eZeroOfInv G A x) = x := by
  apply Subtype.ext
  change (Rep.Hom.hom (eZeroOfInv G A x)) (1 : SSGRoute.PTExt.Coeff) = (x : A)
  rw [show (Rep.Hom.hom (eZeroOfInv G A x)) (1 : SSGRoute.PTExt.Coeff)
        = (Rep.Hom.hom (eZeroOfInv G A x)).toLinearMap 1 from rfl,
      eZeroOfInv_hom_apply, LinearMap.toSpanSingleton_apply_one]

lemma eZeroOfInv_eZeroToInv (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (f : SSGRoute.PTExt.unitRep G ⟶ A) : eZeroOfInv G A (eZeroToInv G A f) = f := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply LinearMap.ext_ring
  rw [eZeroOfInv_hom_apply, LinearMap.toSpanSingleton_apply_one]
  rfl

/-- `(unitRep G ⟶ A) ≃+ A.ρ.invariants`, by evaluation at `1`. -/
def eZeroUnitHomEquiv (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (SSGRoute.PTExt.unitRep G ⟶ A) ≃+ ↥A.ρ.invariants where
  toFun := eZeroToInv G A
  invFun := eZeroOfInv G A
  left_inv := eZeroOfInv_eZeroToInv G A
  right_inv := eZeroToInv_eZeroOfInv G A
  map_add' f g := by
    apply Subtype.ext
    rfl

/-! ## Naturality in `A` -/

lemma eZeroToInv_naturality (G : Type) [Group G] (A B : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : A ⟶ B) (f : SSGRoute.PTExt.unitRep G ⟶ A) :
    eZeroToInv G B (f ≫ φ) = (Rep.invariantsFunctor SSGRoute.PTExt.Coeff G).map φ (eZeroToInv G A f) := by
  apply Subtype.ext
  show ((Rep.Hom.hom φ).comp (Rep.Hom.hom f)) 1 = (Rep.Hom.hom φ) ((Rep.Hom.hom f) 1)
  rw [show ((Rep.Hom.hom φ).comp (Rep.Hom.hom f)) 1
        = ((Rep.Hom.hom φ).comp (Rep.Hom.hom f)).toLinearMap 1 from rfl,
      IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply]

lemma eZeroOfInv_naturality (G : Type) [Group G] (A B : Rep.{0} SSGRoute.PTExt.Coeff G)
    (φ : A ⟶ B) (x : ↥A.ρ.invariants) :
    eZeroOfInv G B ((Rep.invariantsFunctor SSGRoute.PTExt.Coeff G).map φ x)
      = eZeroOfInv G A x ≫ φ := by
  apply (eZeroUnitHomEquiv G B).injective
  show eZeroToInv G B (eZeroOfInv G B ((Rep.invariantsFunctor SSGRoute.PTExt.Coeff G).map φ x))
      = eZeroToInv G B (eZeroOfInv G A x ≫ φ)
  rw [eZeroToInv_eZeroOfInv, eZeroToInv_naturality, eZeroToInv_eZeroOfInv]

/-! ## The `Ext`-side -/

lemma eZero_linearEquiv₀_mk₀ (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (f : SSGRoute.PTExt.unitRep G ⟶ A) :
    (Abelian.Ext.linearEquiv₀ (R := SSGRoute.PTExt.Coeff)
      (X := SSGRoute.PTExt.unitRep G) (Y := A)) (Abelian.Ext.mk₀ f) = f := by
  apply (Abelian.Ext.mk₀_bijective (SSGRoute.PTExt.unitRep G) A).1
  rw [Abelian.Ext.mk₀_linearEquiv₀_apply]

/-- The main isomorphism `H⁰(G, A) ≃+ extH A 0`. -/
def eZero (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    groupCohomology A 0 ≃+ SSGRoute.PTExt.extH A 0 where
  toFun y := Abelian.Ext.mk₀ (eZeroOfInv G A ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y))
  invFun x := (Iso.toLinearEquiv (groupCohomology.H0Iso A)).symm
    (eZeroToInv G A ((Abelian.Ext.linearEquiv₀ (R := SSGRoute.PTExt.Coeff)
      (X := SSGRoute.PTExt.unitRep G) (Y := A)) x))
  left_inv y := by
    show (Iso.toLinearEquiv (groupCohomology.H0Iso A)).symm
        (eZeroToInv G A ((Abelian.Ext.linearEquiv₀ (R := SSGRoute.PTExt.Coeff)
          (X := SSGRoute.PTExt.unitRep G) (Y := A))
            (Abelian.Ext.mk₀
              (eZeroOfInv G A ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y))))) = y
    rw [eZero_linearEquiv₀_mk₀, eZeroToInv_eZeroOfInv]
    exact (Iso.toLinearEquiv (groupCohomology.H0Iso A)).left_inv y
  right_inv x := by
    show Abelian.Ext.mk₀ (eZeroOfInv G A
        ((Iso.toLinearEquiv (groupCohomology.H0Iso A))
          ((Iso.toLinearEquiv (groupCohomology.H0Iso A)).symm
            (eZeroToInv G A ((Abelian.Ext.linearEquiv₀ (R := SSGRoute.PTExt.Coeff)
              (X := SSGRoute.PTExt.unitRep G) (Y := A)) x))))) = x
    rw [LinearEquiv.apply_symm_apply, eZeroOfInv_eZeroToInv]
    exact Abelian.Ext.mk₀_linearEquiv₀_apply x
  map_add' y₁ y₂ := by
    have h1 : (Iso.toLinearEquiv (groupCohomology.H0Iso A)) (y₁ + y₂)
        = (Iso.toLinearEquiv (groupCohomology.H0Iso A)) y₁
          + (Iso.toLinearEquiv (groupCohomology.H0Iso A)) y₂ := map_add _ _ _
    have h2 : eZeroOfInv G A ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y₁
          + (Iso.toLinearEquiv (groupCohomology.H0Iso A)) y₂)
        = eZeroOfInv G A ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y₁)
          + eZeroOfInv G A ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y₂) :=
      (eZeroUnitHomEquiv G A).symm.map_add _ _
    rw [h1, h2, Abelian.Ext.mk₀_add]

lemma eZero_apply (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (y : groupCohomology A 0) :
    eZero G A y
      = Abelian.Ext.mk₀ (eZeroOfInv G A ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y)) :=
  rfl

/-! ## Naturality of `H⁰` -/

lemma H0_map_H0Iso (G : Type) [Group G] (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B)
    (y : groupCohomology A 0) :
    (Iso.toLinearEquiv (groupCohomology.H0Iso B))
        ((groupCohomology.map (MonoidHom.id G) φ 0).hom y)
      = (Rep.invariantsFunctor SSGRoute.PTExt.Coeff G).map φ
          ((Iso.toLinearEquiv (groupCohomology.H0Iso A)) y) :=
  groupCohomology.map_id_comp_H0Iso_hom_apply (k := SSGRoute.PTExt.Coeff) (G := G) φ y

/-! ## The target -/

/-- **Group cohomology is `Ext`-cohomology in degree `0`, naturally in the coefficients.** -/
theorem exists_e_zero_natural (G : Type) [Group G] :
    ∃ (e : ∀ (A : Rep.{0} SSGRoute.PTExt.Coeff G),
        groupCohomology A 0 ≃+ SSGRoute.PTExt.extH A 0),
      ∀ (A B : Rep.{0} SSGRoute.PTExt.Coeff G) (φ : A ⟶ B) (y : groupCohomology A 0),
        e B ((groupCohomology.map (MonoidHom.id G) φ 0).hom y)
          = (e A y).comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 0) := by
  refine ⟨fun A => eZero G A, ?_⟩
  intro A B φ y
  rw [eZero_apply, eZero_apply, H0_map_H0Iso, eZeroOfInv_naturality,
    Abelian.Ext.mk₀_comp_mk₀]

end Work.SSGRoute
