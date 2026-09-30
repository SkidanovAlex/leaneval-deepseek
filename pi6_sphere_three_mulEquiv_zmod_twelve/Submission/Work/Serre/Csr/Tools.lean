import Mathlib
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.relChains_compl_union_free
import Submission.Work.Serre.csrDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Tools for the per-cell computation `Work.Serre.csrPerCell`

Bookkeeping tools about the relative singular chain complex `C_*(X,A)` over `ℤ`:

* `Work.Serre.subtypeSubtypeHomeo` — the canonical homeomorphism between the two models of a subset
  `A ⊆ B` of a space (`↥A` and `{x : ↥B | (x : X) ∈ A}`);
* `Work.Serre.isIso_subtypeIncl_of_isZero_relChains` — if the pair `(B,A)` is relatively acyclic,
  the inclusion `↥A → ↥B` is a quasi-isomorphism.  This is the form in which the compression
  engine (`Work.Serre.isZero_relChains_preimage_of_base_compress`) produces the *absolute*
  isomorphisms needed by the five lemma `Work.Cohomology.relChainsMapOf_isIso`.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

namespace Work.Serre

noncomputable section

/-- The inclusion `↥A → ↥B` of subtypes, for `A ⊆ B`. -/
def subtypeInclCM {X : Type} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) : C(↥A, ↥B) where
  toFun a := ⟨a.1, hAB a.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val (fun a => hAB a.2)

/-- The canonical map `{x : ↥B // (x : X) ∈ A} → ↥A`, for `A ⊆ B`. -/
def subtypeOfSubtypeCM {X : Type} [TopologicalSpace X] {A B : Set X} :
    C({x : ↥B | (x : X) ∈ A}, ↥A) where
  toFun y := ⟨(y.1 : X), y.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)


/-- The inverse of `subtypeOfSubtypeCM`, as a continuous map. -/
def subtypeOfSubtypeInvCM {X : Type} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    C(↥A, {x : ↥B | (x : X) ∈ A}) where
  toFun a := ⟨⟨a.1, hAB a.2⟩, a.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun a => hAB a.2))
      (fun a => a.2)

/-- The canonical map `{x : ↥B // (x : X) ∈ A} → ↥B`. -/
def subtypeOfSubtypeValCM {X : Type} [TopologicalSpace X] {A B : Set X} :
    C({x : ↥B | (x : X) ∈ A}, ↥B) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The canonical homeomorphism `{x : ↥B // (x : X) ∈ A} ≃ₜ ↥A` for `A ⊆ B`. -/
def subtypeSubtypeHomeo {X : Type} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    {x : ↥B | (x : X) ∈ A} ≃ₜ ↥A where
  toFun := subtypeOfSubtypeCM
  invFun a := ⟨⟨a.1, hAB a.2⟩, a.2⟩
  left_inv x := Subtype.ext rfl
  right_inv a := Subtype.ext rfl
  continuous_toFun := (subtypeOfSubtypeCM (A := A) (B := B)).continuous
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun a => hAB a.2))
      (fun a => a.2)

/-- **A chain map whose homology map is an isomorphism in a degree gives an isomorphism of the
homology groups in that degree.** -/
theorem nonempty_homologyIso_of_isIso_homologyMap {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (φ : C ⟶ D) (k : ℕ) (h : IsIso (HomologicalComplex.homologyMap φ k)) :
    Nonempty (C.homology k ≅ D.homology k) :=
  ⟨asIso (HomologicalComplex.homologyMap φ k)⟩

/-- **The pair LES criterion.**  If the pair `(B,A)` (subsets of a space `X`) has vanishing
relative homology in every degree, then the inclusion `↥A → ↥B` is a quasi-isomorphism. -/
theorem isIso_subtypeIncl_of_isZero_relChains {X : Type} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B)
    (h : ∀ k, IsZero ((Work.Cohomology.relChains (TopCat.of ↥B)
      {x : ↥B | (x : X) ∈ A}).homology k)) :
    ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
        (TopCat.ofHom (subtypeInclCM hAB))) k) := by
  intro k
  -- the canonical inclusion `{x : ↥B // (x : X) ∈ A} ⟶ ↥B` is a quasi-isomorphism
  have hcan : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥B)
        (TopCat.ofHom (subtypeOfSubtypeValCM (A := A) (B := B)))) k) :=
    Work.Cohomology.isIso_homologyMap_of_acyclic
      (Work.Cohomology.hPairShort_shortExact (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}) k
      (h (k+1)) (h k)
  -- the morphism of the canonical homeomorphism
  let ψ : TopCat.of {x : ↥B | (x : X) ∈ A} ⟶ TopCat.of ↥A :=
    (TopCat.isoOfHomeo (subtypeSubtypeHomeo (X := X) hAB)).hom
  have hψval : ∀ y : {x : ↥B | (x : X) ∈ A},
      (ψ : {x : ↥B | (x : X) ∈ A} → ↥A) y = ⟨(y.1 : X), y.2⟩ := fun y => rfl
  haveI hψiso : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B | (x : X) ∈ A})
      (TopCat.of ↥A) ψ) := by
    have hmap : Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A) ψ
        = ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map ψ := rfl
    rw [hmap]
    infer_instance
  -- the decomposition of the canonical inclusion
  have hdecomp : (TopCat.ofHom (subtypeOfSubtypeValCM (A := A) (B := B))
      : TopCat.of {x : ↥B | (x : X) ∈ A} ⟶ TopCat.of ↥B)
      = ψ ≫ (TopCat.ofHom (subtypeInclCM hAB) : TopCat.of ↥A ⟶ TopCat.of ↥B) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    rfl
  have hchain : Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥B)
      (TopCat.ofHom (subtypeOfSubtypeValCM (A := A) (B := B)))
      = Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A) ψ
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
          (TopCat.ofHom (subtypeInclCM hAB)) := by
    rw [hdecomp, Work.Cohomology.chainMap_comp_relChains]
  rw [hchain, HomologicalComplex.homologyMap_comp] at hcan
  -- conclude
  haveI hcanI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A) ψ) k
      ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
          (TopCat.ofHom (subtypeInclCM hAB))) k) := hcan
  have hV : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥A)
        (TopCat.of ↥B) (TopCat.ofHom (subtypeInclCM hAB))) k
      = CategoryTheory.inv (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A) ψ) k)
        ≫ (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of {x : ↥B | (x : X) ∈ A}) (TopCat.of ↥A) ψ) k
          ≫ HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of ↥A)
              (TopCat.of ↥B) (TopCat.ofHom (subtypeInclCM hAB))) k) := by
    rw [← Category.assoc, CategoryTheory.IsIso.inv_hom_id, Category.id_comp]
  rw [hV]
  infer_instance


/-- The canonical inclusion between the "double subtype" models of two subset pairs. -/
def doubleSubtypeInclCM {X : Type} [TopologicalSpace X] {A₀ A₁ B₀ B₁ : Set X}
    (hA : A₀ ⊆ A₁) (hB : B₀ ⊆ B₁) :
    C({x : ↥B₀ | (x : X) ∈ A₀}, {x : ↥B₁ | (x : X) ∈ A₁}) :=
  ⟨fun y => ⟨⟨(y.1 : X), hB y.1.2⟩, hA y.2⟩, by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ (fun y => hB y.1.2)) (fun y => hA y.2)
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- **Transport of quasi-isomorphism through the two models of a subset.**  If the inclusion
`A₀ → A₁` is a quasi-isomorphism then so is the corresponding inclusion of the "double subtype"
models `{x : ↥B₀ // (x : X) ∈ A₀} → {x : ↥B₁ // (x : X) ∈ A₁}`. -/
theorem isIso_chainMap_doubleSubtype {X : Type} [TopologicalSpace X] {A₀ A₁ B₀ B₁ : Set X}
    (hA : A₀ ⊆ A₁) (hB : B₀ ⊆ B₁) (hA₀ : A₀ ⊆ B₀) (hA₁ : A₁ ⊆ B₁)
    (h : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥A₀) (TopCat.of ↥A₁)
        (TopCat.ofHom (subtypeInclCM hA))) k)) :
    ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B₀ | (x : X) ∈ A₀})
        (TopCat.of {x : ↥B₁ | (x : X) ∈ A₁})
        (TopCat.ofHom (doubleSubtypeInclCM hA hB))) k) := by
  have key : (TopCat.ofHom (doubleSubtypeInclCM hA hB)
      : TopCat.of {x : ↥B₀ | (x : X) ∈ A₀} ⟶ TopCat.of {x : ↥B₁ | (x : X) ∈ A₁})
      = (TopCat.ofHom (subtypeOfSubtypeCM (A := A₀) (B := B₀)))
        ≫ ((TopCat.ofHom (subtypeInclCM hA))
          ≫ (TopCat.ofHom (subtypeOfSubtypeInvCM hA₁))) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  haveI h₁ : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B₀ | (x : X) ∈ A₀})
      (TopCat.of ↥A₀) (TopCat.ofHom (subtypeOfSubtypeCM (A := A₀) (B := B₀)))) := by
    have hEq : (TopCat.ofHom (subtypeOfSubtypeCM (A := A₀) (B := B₀))
        : TopCat.of {x : ↥B₀ | (x : X) ∈ A₀} ⟶ TopCat.of ↥A₀)
        = (TopCat.isoOfHomeo (subtypeSubtypeHomeo hA₀)).hom := by
      rw [TopCat.isoOfHomeo_hom]
      rfl
    rw [hEq]
    infer_instance
  haveI h₂ : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥A₁)
      (TopCat.of {x : ↥B₁ | (x : X) ∈ A₁}) (TopCat.ofHom (subtypeOfSubtypeInvCM hA₁))) := by
    have hEq : (TopCat.ofHom (subtypeOfSubtypeInvCM hA₁)
        : TopCat.of ↥A₁ ⟶ TopCat.of {x : ↥B₁ | (x : X) ∈ A₁})
        = (TopCat.isoOfHomeo (subtypeSubtypeHomeo hA₁)).inv := by
      rw [TopCat.isoOfHomeo_inv]
      rfl
    rw [hEq]
    infer_instance
  intro k
  rw [key, Work.Cohomology.chainMap_comp_relChains, Work.Cohomology.chainMap_comp_relChains,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI := h k
  infer_instance

end

end Work.Serre
