import Mathlib
import Submission.Work.Cohomology.cappedPairDefs
import Submission.Work.Cohomology.relComplexMapDualZ
import Submission.Work.Cohomology.dualZMapRelChainsMapIsIso
import Submission.Work.Cohomology.relComplexMapCollarIsIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pinned pair identification `(X, D⁸) ≅ (Vk(-2), Mk(-2))`

For a capping datum `D` on the pair `(Vk (-2), ℝ⁸)` with `D.U = collar (-2)`, the open embedding
`D.ιX : Vk (-2) → X = cappedSpace D` carries the sphere bundle `Mk (-2) = range (mkToVkFun (-2))`
into the cap `A = range D.ιY`, hence induces a map of pairs `(Vk(-2), Mk(-2)) → (X, A)` and a map

`Hⁿ(X, A; ℤ) ⟶ Hⁿ(Vk(-2), Mk(-2); ℤ)`.

This file proves that this map is an isomorphism in every degree (*pinned*: it is the map induced by
`D.ιX`, not merely an abstract isomorphism), which allows cup products to be transported along the
identification `(X, D⁸) ≅ (Vk(-2), Mk(-2))` via `Work.Cohomology.relCupHNatural`.

The map `D.ιX` factorises, on the level of pairs, as

`(Vk(-2), Mk(-2)) --incl--> (Vk(-2), collar(-2)) --≅--> (range D.ιX, A ∩ range D.ιX)
   --incl--> (X, A)`

and each of the three pieces induces an isomorphism on relative cohomology:

* the first is the inclusion of a deformation retract (`Work.Milnor.collar_homotopyEquiv_Mk` and the
  five lemma, `relComplexMapCollarIsIso`);
* the second is an isomorphism of pairs (the open embedding `D.ιX` restricted to its image,
  `relComplexMap_iso_of_isIso_pairs`);
* the third is an excision (`relComplexMap_excision_isIso`, from the naturality of the duality
  identification `relComplexMapDualZ` and the dualised excision `dualZMapRelChainsMapIsIso`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-! ## Generalities on the relative pair map -/

/-- **A map of pairs which is an isomorphism of the underlying spaces is an isomorphism on relative
cohomology.** -/
theorem relComplexMap_iso_of_isIso_pairs (R : Type) [CommRing R] {X₁ X₂ : TopCat}
    (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (g : X₂ ⟶ X₁)
    (hg : ∀ y ∈ A₂, g y ∈ A₁)
    (hfg : CategoryTheory.CategoryStruct.comp f g = CategoryTheory.CategoryStruct.id X₁)
    (hgf : CategoryTheory.CategoryStruct.comp g f = CategoryTheory.CategoryStruct.id X₂)
    (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ f h) n) := by
  have h1 : CategoryTheory.CategoryStruct.comp (relComplexMap R A₁ A₂ f h)
      (relComplexMap R A₂ A₁ g hg) = CategoryTheory.CategoryStruct.id (relComplex R X₂ A₂) := by
    rw [← relComplexMap_comp R A₂ A₁ A₂ g f hg h]
    refine (relComplexMap_congr R A₂ A₂ hgf (fun x hx => h (g x) (hg x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact relComplexMap_id R A₂ (fun x hx => by simpa using hx)
  have h2 : CategoryTheory.CategoryStruct.comp (relComplexMap R A₂ A₁ g hg)
      (relComplexMap R A₁ A₂ f h) = CategoryTheory.CategoryStruct.id (relComplex R X₁ A₁) := by
    rw [← relComplexMap_comp R A₁ A₂ A₁ f g h hg]
    refine (relComplexMap_congr R A₁ A₁ hfg (fun x hx => hg (f x) (h x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact relComplexMap_id R A₁ (fun x hx => by simpa using hx)
  haveI : CategoryTheory.IsIso (relComplexMap R A₁ A₂ f h) :=
    ⟨relComplexMap R A₂ A₁ g hg, h1, h2⟩
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
    (relComplexMap R A₁ A₂ f h)

/-- **The pair map of a composite is an isomorphism on relative cohomology when both factors
are.**  The hypothesis on `h` is given explicitly so that the canonical hypothesis term of
`relComplexMap_comp` never has to be matched. -/
theorem isIso_relComplexMap_comp_of_isIso (R : Type) [CommRing R] {X₀ X₁ X₂ : TopCat}
    (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂) (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
    (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) (n : ℕ)
    (h : ∀ x ∈ A₀, (CategoryTheory.CategoryStruct.comp f g) x ∈ A₂)
    (h₂ : CategoryTheory.IsIso (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ g hg) n))
    (h₁ : CategoryTheory.IsIso (HomologicalComplex.homologyMap (relComplexMap R A₀ A₁ f hf) n)) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relComplexMap R A₀ A₂
        (CategoryTheory.CategoryStruct.comp f g) h) n) := by
  have heq : relComplexMap R A₀ A₂ (CategoryTheory.CategoryStruct.comp f g) h
      = relComplexMap R A₀ A₂ (CategoryTheory.CategoryStruct.comp f g)
          (fun x hx => hg (f x) (hf x hx)) :=
    relComplexMap_congr R A₀ A₂ rfl h (fun x hx => hg (f x) (hf x hx))
  rw [heq, relComplexMap_comp R A₀ A₁ A₂ f g hf hg, HomologicalComplex.homologyMap_comp]
  exact inferInstance

/-! ## The pair map of the inclusion `(U, U ∩ A) ⊆ (X, A)` written in the two available ways -/

/-- The composite `cokernel.π ≫ relChainsMapOf` is the chain map followed by `cokernel.π`. -/
theorem cokernel_π_relChainsMapOf {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B) (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    cokernel.π (inclChains X A) ≫ relChainsMapOf X Y A B f g w
      = chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B) := by
  rw [relChainsMapOf]
  exact cokernel_π_map (inclChains X A) (inclChains Y B)
    (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f) _

/-- **The pair map of the inclusion `(U, U ∩ A) ⊆ (X, A)` is the same whether it is written with
`relMapSub` (as in `relComplexMapDualZ`) or with `inclInterA` (as in `relChainsMap`).** -/
theorem relChainsMapOf_relMapSub_eq_relChainsMap (X : TopCat) (U A : Set X)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A}, (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    relChainsMapOf (TopCat.of U) X {y : U | (y : X) ∈ A} A (subtypeIncl X U)
        (relMapSub {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)
        (relMapSub_spec {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)
      = relChainsMap X U A := by
  rw [relChainsMap]
  apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) {y : U | (y : X) ∈ A}))).1
  rw [cokernel_π_relChainsMapOf, cokernel_π_relChainsMapOf]

/-! ## Excision, pinned

The two ingredients are delegated: `relComplexMapDualZ` (the relation between the pair map and the
map of `ℤ`-dual complexes) and `dualZMapRelChainsMapIsIso` (the dualised excision).  They are
stubbed here while in flight. -/

/-- **The inclusion of pairs `(U, U ∩ A) → (X, A)` induces an isomorphism on relative cohomology**
whenever `U, A` are open and cover `X`. -/
theorem relComplexMap_excision_isIso (R : Type) [CommRing R] (X : TopCat) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A},
      (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap R {y : U | (y : X) ∈ A} A (subtypeIncl X U) h) n) := by
  rw [relComplexMapDualZ R {y : U | (y : X) ∈ A} A (subtypeIncl X U) h]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  rw [relChainsMapOf_relMapSub_eq_relChainsMap X U A h]
  haveI hB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (dualZMap R (relChains (TopCat.of U) {y : U | (y : X) ∈ A}) (relChains X A)
        (relChainsMap X U A)) n) :=
    dualZMapRelChainsMapIsIso R X U A hU hA hcov n
  haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Iso.inv (relZIsoComplex R X A)) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (CategoryTheory.Iso.inv (relZIsoComplex R X A))
  haveI h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Iso.hom (relZIsoComplex R (TopCat.of U) {y : U | (y : X) ∈ A})) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (CategoryTheory.Iso.hom (relZIsoComplex R (TopCat.of U) {y : U | (y : X) ∈ A}))
  exact inferInstance

/-! ## The open embedding `D.ιX` as a homeomorphism onto its image -/

section Capped

variable (D : Work.Milnor.CapData)

/-- The capped space `X`, as a topological space. -/
abbrev cappedPairX : TopCat := TopCat.of (Work.Milnor.cappedSpace D)

/-- The open piece `U = D.ιX '' Vk(-2)` of the capped space. -/
abbrev cappedPairU : Set ↥(cappedPairX D) := Set.range D.ιX

/-- The cap `A = D.ιY '' ℝ⁸`. -/
abbrev cappedPairA : Set ↥(cappedPairX D) := Set.range D.ιY

/-- The relative part of the cap inside `U`. -/
abbrev cappedPairArel : Set ↥(TopCat.of (cappedPairU D)) :=
  {y | (y : cappedPairX D) ∈ cappedPairA D}

/-- The unit sphere bundle `Mk(-2) = range (mkToVkFun (-2))` inside `Vk(-2)`. -/
abbrev cappedPairS : Set ↥(TopCat.of (Submission.Milnor.Vk (-2))) :=
  Set.range (Work.Milnor.mkToVkFun (-2))

/-- The collar `{1/2 < ν}`, with the type of a subset of `TopCat.of (Vk (-2))`. -/
abbrev cappedPairK : Set ↥(TopCat.of (Submission.Milnor.Vk (-2))) := Work.Milnor.collar (-2)

/-- The open embedding `D.ιX`, as a homeomorphism onto its image. -/
def cappedPairHomeo : Submission.Milnor.Vk (-2) ≃ₜ ↥(cappedPairU D) :=
  D.isOpenEmbedding_ιX.toIsEmbedding.toHomeomorph

/-- `D.ιX` as a morphism of topological spaces onto its image. -/
def cappedPairE : TopCat.of (Submission.Milnor.Vk (-2)) ⟶ TopCat.of (cappedPairU D) :=
  TopCat.ofHom ⟨cappedPairHomeo D, (cappedPairHomeo D).continuous⟩

/-- The inverse of `cappedPairE`. -/
def cappedPairEInv : TopCat.of (cappedPairU D) ⟶ TopCat.of (Submission.Milnor.Vk (-2)) :=
  TopCat.ofHom ⟨(cappedPairHomeo D).symm, (cappedPairHomeo D).symm.continuous⟩

theorem cappedPairE_apply (p : Submission.Milnor.Vk (-2)) :
    ((cappedPairE D p : ↥(cappedPairU D)) : Work.Milnor.cappedSpace D) = D.ιX p :=
  Topology.IsEmbedding.toHomeomorph_apply_coe _ p

theorem cappedPairE_comp_cappedPairEInv :
    CategoryTheory.CategoryStruct.comp (cappedPairE D) (cappedPairEInv D)
      = CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))) := by
  apply TopCat.ext
  intro p
  show (cappedPairHomeo D).symm (cappedPairHomeo D p) = p
  exact (cappedPairHomeo D).symm_apply_apply p

theorem cappedPairEInv_comp_cappedPairE :
    CategoryTheory.CategoryStruct.comp (cappedPairEInv D) (cappedPairE D)
      = CategoryTheory.CategoryStruct.id (TopCat.of (cappedPairU D)) := by
  apply TopCat.ext
  intro y
  show cappedPairHomeo D ((cappedPairHomeo D).symm y) = y
  exact (cappedPairHomeo D).apply_symm_apply y

theorem cappedPairE_comp_incl :
    CategoryTheory.CategoryStruct.comp (cappedPairE D)
        (subtypeIncl (cappedPairX D) (cappedPairU D))
      = TopCat.ofHom ⟨D.ιX, D.continuous_ιX⟩ := by
  apply TopCat.ext
  intro p
  exact cappedPairE_apply D p

theorem cappedPairEInv_apply_cappedPairE (p : Submission.Milnor.Vk (-2)) :
    cappedPairEInv D (cappedPairE D p) = p :=
  (cappedPairHomeo D).symm_apply_apply p

end Capped

/-! ## The collar step (delegated, in explicit form) -/

/-- **The collar step of the pair identification**, in the explicit form needed below. -/
theorem relComplexMapCollarIsIso' (n : ℕ)
    (h : ∀ x ∈ cappedPairS,
      (ConcreteCategory.hom
          (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))) x
        ∈ cappedPairK) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of (Submission.Milnor.Vk (-2)))
        (X₂ := TopCat.of (Submission.Milnor.Vk (-2))) ℤ cappedPairS cappedPairK
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) h) n) := by
  have heq : relComplexMap ℤ cappedPairS cappedPairK
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) h
      = relComplexMap ℤ cappedPairS cappedPairK
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))
        (by
          intro x hx
          obtain ⟨q, rfl⟩ := hx
          exact Work.Milnor.mem_collar.mpr
            (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q)) :=
    relComplexMap_congr ℤ cappedPairS cappedPairK rfl h _
  rw [heq]
  exact relComplexMapCollarIsIso n

/-! ## The pinned pair identification -/

/-- **The pinned pair identification**: the map of pairs
`(Vk(-2), Mk(-2)) ⟶ (X, D⁸)` induced by the open embedding `D.ιX` induces an isomorphism on
relative cohomology, when `D.U = collar (-2)`. -/
theorem cappedPairMapIso (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (R := ℤ) (Set.range (Work.Milnor.mkToVkFun (-2)))
        (Set.range D.ιY) (TopCat.ofHom ⟨D.ιX, D.continuous_ιX⟩)
        (by
          intro x hx
          obtain ⟨q, rfl⟩ := hx
          refine ⟨D.φ (Work.Milnor.mkToVkFun (-2) q), ?_⟩
          exact D.ιY_eq_ιX_iff.mpr ⟨by
            rw [hU]
            exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q), rfl⟩)) n) := by
  have hRestr : ∀ y ∈ cappedPairArel D,
      (ConcreteCategory.hom (subtypeIncl (cappedPairX D) (cappedPairU D))) y ∈ cappedPairA D :=
    fun y hy => hy
  have hCapE : ∀ x ∈ cappedPairS, (ConcreteCategory.hom (cappedPairE D)) x ∈ cappedPairArel D := by
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    have hxU : Work.Milnor.mkToVkFun (-2) q ∈ D.U := by
      rw [hU]
      exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q)
    change ((cappedPairE D (Work.Milnor.mkToVkFun (-2) q) : ↥(cappedPairU D)) :
      Work.Milnor.cappedSpace D) ∈ cappedPairA D
    rw [cappedPairE_apply D (Work.Milnor.mkToVkFun (-2) q)]
    exact ⟨D.φ (Work.Milnor.mkToVkFun (-2) q),
      (D.ιX_eq_ιY_iff.mpr ⟨hxU, rfl⟩).symm⟩
  have hCapE' : ∀ x ∈ Work.Milnor.collar (-2),
      (ConcreteCategory.hom (cappedPairE D)) x ∈ cappedPairArel D := by
    intro x hx
    have hxU : x ∈ D.U := by rw [hU]; exact hx
    change ((cappedPairE D x : ↥(cappedPairU D)) : Work.Milnor.cappedSpace D) ∈ cappedPairA D
    rw [cappedPairE_apply D x]
    exact ⟨D.φ x, (D.ιX_eq_ιY_iff.mpr ⟨hxU, rfl⟩).symm⟩
  have hCollar : ∀ x ∈ cappedPairS,
      (ConcreteCategory.hom
          (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))) x
        ∈ Work.Milnor.collar (-2) := by
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q)
  have hInv : ∀ y ∈ cappedPairArel D,
      (ConcreteCategory.hom (cappedPairEInv D)) y ∈ Work.Milnor.collar (-2) := by
    intro y hy
    have hyA : (y : Work.Milnor.cappedSpace D) ∈ cappedPairA D := hy
    obtain ⟨p, hp⟩ := y.2
    have hsub : y = cappedPairE D p := by
      apply Subtype.ext
      rw [cappedPairE_apply D p]
      exact hp.symm
    rw [hsub, cappedPairEInv_apply_cappedPairE D p]
    have hpA : D.ιX p ∈ cappedPairA D := by rw [hp]; exact hyA
    obtain ⟨z, hz⟩ := hpA
    have hpU : p ∈ D.U := (D.ιY_eq_ιX_iff.mp hz).choose
    rwa [hU] at hpU
  have hExIso : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of (cappedPairU D)) (X₂ := cappedPairX D) ℤ
        (cappedPairArel D) (cappedPairA D)
        (subtypeIncl (cappedPairX D) (cappedPairU D)) hRestr) n) :=
    relComplexMap_excision_isIso ℤ (cappedPairX D) (cappedPairU D) (cappedPairA D)
      D.isOpenEmbedding_ιX.isOpen_range D.isOpenEmbedding_ιY.isOpen_range
      D.range_ιX_union_range_ιY n hRestr
  have hCapE' : ∀ x ∈ cappedPairK,
      (ConcreteCategory.hom (cappedPairE D)) x ∈ cappedPairArel D := by
    intro x hx
    have hxU : x ∈ D.U := by rw [hU]; exact hx
    change ((cappedPairE D x : ↥(cappedPairU D)) : Work.Milnor.cappedSpace D) ∈ cappedPairA D
    rw [cappedPairE_apply D x]
    exact ⟨D.φ x, (D.ιX_eq_ιY_iff.mpr ⟨hxU, rfl⟩).symm⟩
  have hCollar : ∀ x ∈ cappedPairS,
      (ConcreteCategory.hom
          (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))) x
        ∈ cappedPairK := by
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q)
  have hInv : ∀ y ∈ cappedPairArel D,
      (ConcreteCategory.hom (cappedPairEInv D)) y ∈ cappedPairK := by
    intro y hy
    have hyA : (y : Work.Milnor.cappedSpace D) ∈ cappedPairA D := hy
    obtain ⟨p, hp⟩ := y.2
    have hsub : y = cappedPairE D p := by
      apply Subtype.ext
      rw [cappedPairE_apply D p]
      exact hp.symm
    rw [hsub, cappedPairEInv_apply_cappedPairE D p]
    have hpA : D.ιX p ∈ cappedPairA D := by rw [hp]; exact hyA
    obtain ⟨z, hz⟩ := hpA
    have hpU : p ∈ D.U := (D.ιY_eq_ιX_iff.mp hz).choose
    rwa [hU] at hpU
  have hPairsIso : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of (Submission.Milnor.Vk (-2)))
        (X₂ := TopCat.of (cappedPairU D)) ℤ cappedPairK (cappedPairArel D)
        (cappedPairE D) hCapE') n) :=
    relComplexMap_iso_of_isIso_pairs ℤ cappedPairK (cappedPairArel D) (cappedPairE D) hCapE'
      (cappedPairEInv D) hInv (cappedPairE_comp_cappedPairEInv D)
      (cappedPairEInv_comp_cappedPairE D) n
  have hCollarIso : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of (Submission.Milnor.Vk (-2)))
        (X₂ := TopCat.of (Submission.Milnor.Vk (-2))) ℤ cappedPairS cappedPairK
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) hCollar) n) :=
    relComplexMapCollarIsIso' n hCollar
  have hMidHyp : ∀ x ∈ cappedPairS,
      (ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))
        (cappedPairE D))) x ∈ cappedPairArel D :=
    fun x hx => hCapE' ((CategoryTheory.CategoryStruct.id
      (TopCat.of (Submission.Milnor.Vk (-2)))) x) (hCollar x hx)
  have hMidIso : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of (Submission.Milnor.Vk (-2)))
        (X₂ := TopCat.of (cappedPairU D)) ℤ cappedPairS (cappedPairArel D)
        (cappedPairE D) hCapE) n) := by
    have heq : relComplexMap ℤ cappedPairS (cappedPairArel D) (cappedPairE D) hCapE
        = relComplexMap ℤ cappedPairS (cappedPairArel D)
            (CategoryTheory.CategoryStruct.comp
              (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))
              (cappedPairE D)) hMidHyp := by
      refine (relComplexMap_congr ℤ cappedPairS (cappedPairArel D) ?_ hCapE hMidHyp).symm
      exact Category.id_comp (cappedPairE D)
    rw [heq]
    exact isIso_relComplexMap_comp_of_isIso ℤ cappedPairS cappedPairK (cappedPairArel D)
      (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))
      (cappedPairE D) hCollar hCapE' n hMidHyp hPairsIso hCollarIso
  have hFinalHyp : ∀ x ∈ cappedPairS,
      (ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp (cappedPairE D)
        (subtypeIncl (cappedPairX D) (cappedPairU D)))) x ∈ cappedPairA D :=
    fun x hx => hRestr (cappedPairE D x) (hCapE x hx)
  have hEqGoal : relComplexMap ℤ cappedPairS (cappedPairA D)
        (TopCat.ofHom ⟨D.ιX, D.continuous_ιX⟩)
        (by
          intro x hx
          obtain ⟨q, rfl⟩ := hx
          refine ⟨D.φ (Work.Milnor.mkToVkFun (-2) q), ?_⟩
          exact D.ιY_eq_ιX_iff.mpr ⟨by
            rw [hU]
            exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q), rfl⟩)
      = relComplexMap ℤ cappedPairS (cappedPairA D)
          (CategoryTheory.CategoryStruct.comp (cappedPairE D)
            (subtypeIncl (cappedPairX D) (cappedPairU D))) hFinalHyp :=
    relComplexMap_congr ℤ cappedPairS (cappedPairA D) (cappedPairE_comp_incl D).symm _ hFinalHyp
  rw [hEqGoal]
  exact isIso_relComplexMap_comp_of_isIso (X₀ := TopCat.of (Submission.Milnor.Vk (-2)))
    (X₁ := TopCat.of (cappedPairU D)) (X₂ := cappedPairX D) ℤ cappedPairS (cappedPairArel D)
    (cappedPairA D) (cappedPairE D) (subtypeIncl (cappedPairX D) (cappedPairU D)) hCapE hRestr n
    hFinalHyp hExIso hMidIso
end

end Work.Cohomology
