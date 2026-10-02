import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Maps of pairs and the relative singular chain complex (ℤ coefficients)

This file provides the functoriality of the relative singular chain complex
`Work.Cohomology.relChains X A = cokernel (C_*(A) → C_*(X))` with respect to a *map of pairs*
`f : X ⟶ Y` with `f '' A ⊆ B`, and derives from it the isomorphism of relative homology groups
induced by a homeomorphism of pairs.

The main result is `Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph`: a homeomorphism
`e : X ≃ₜ Y` with `x ∈ A ↔ e x ∈ B` induces an isomorphism `Hₙ(X,A) ≅ Hₙ(Y,B)`.

The proof is formal: the induced maps on the relative complexes are constructed with
`cokernel.map`, and for a homeomorphism the two induced maps are mutually inverse because
`chainMap` is functorial and `e ∘ e.symm = id` *on the nose* as continuous maps (no homotopy is
involved).
-/

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

variable {X Y : TopCat}

/-- The morphism of `TopCat` underlying a homeomorphism. -/
def sphHomeoHom (e : X ≃ₜ Y) : X ⟶ Y :=
  TopCat.ofHom ⟨e.toFun, e.continuous_toFun⟩

@[simp]
theorem sphHomeoHom_apply (e : X ≃ₜ Y) (x : X) :
    (ConcreteCategory.hom (sphHomeoHom e)) x = e x := rfl

/-- The underlying continuous map of a morphism of `TopCat`. -/
abbrev cmHom (f : X ⟶ Y) : C(↥X, ↥Y) := CategoryTheory.ConcreteCategory.hom f

/-- The restriction of a map of pairs to the first members. -/
def pairRestrict (f : X ⟶ Y) (A : Set X) (B : Set Y) (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a => ⟨f a.1, hf a.1 a.2⟩,
    Continuous.subtype_mk ((cmHom f).continuous.comp continuous_subtype_val) _⟩

/-- The restriction of a map of pairs is compatible with the inclusions of the subspaces. -/
theorem pairRestrict_comp_subtypeIncl (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    pairRestrict f A B hf ≫ Work.Cohomology.subtypeIncl Y B
      = Work.Cohomology.subtypeIncl X A ≫ f := by
  apply TopCat.hom_ext
  ext a
  rfl

/-- The square relating the inclusions of chains with the chain maps induced by a map of pairs
commutes. -/
theorem inclChains_comp_chainMap (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    Work.Cohomology.inclChains X A ≫ Work.Cohomology.chainMap ℤ X Y f
      = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (pairRestrict f A B hf)
        ≫ Work.Cohomology.inclChains Y B := by
  have h := pairRestrict_comp_subtypeIncl f A B hf
  simp only [Work.Cohomology.inclChains, Work.Cohomology.chainMap]
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- **The induced map on relative singular chains of a map of pairs.** -/
def relChainsMapOf (f : X ⟶ Y) (A : Set X) (B : Set Y) (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    Work.Cohomology.relChains X A ⟶ Work.Cohomology.relChains Y B :=
  cokernel.map (Work.Cohomology.inclChains X A) (Work.Cohomology.inclChains Y B)
    (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (pairRestrict f A B hf))
    (Work.Cohomology.chainMap ℤ X Y f) (inclChains_comp_chainMap f A B hf)

/-- The compatibility of `relChainsMapOf` with the projections onto the relative complexes. -/
theorem π_comp_relChainsMapOf (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    cokernel.π (Work.Cohomology.inclChains X A) ≫ relChainsMapOf f A B hf
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B) := by
  rw [relChainsMapOf]
  exact cokernel.π_desc _ _ _

end

end Work.StemsB

namespace Work.StemsB

noncomputable section

variable {X Y Z : TopCat}

/-- Composition of the chain maps induced by continuous maps. -/
theorem chainMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap ℤ X Y f ≫ Work.Cohomology.chainMap ℤ Y Z g
      = Work.Cohomology.chainMap ℤ X Z (f ≫ g) :=
  (Functor.map_comp _ f g).symm

/-- The chain map induced by the identity is the identity. -/
theorem chainMap_id :
    Work.Cohomology.chainMap ℤ X X (𝟙 X) = 𝟙 (Work.Cohomology.singularChains ℤ X) :=
  show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (𝟙 X) = 𝟙 _ from CategoryTheory.Functor.map_id _ X

/-- The inclusion condition for the inverse homeomorphism. -/
theorem homeomorph_symm_mem {e : X ≃ₜ Y} {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) (y : Y) : y ∈ B ↔ e.symm y ∈ A := by
  have h := hAB (e.symm y)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The membership condition transported along `sphHomeoHom`. -/
theorem homeoPairMem {e : X ≃ₜ Y} {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) : ∀ x : X, x ∈ A → (sphHomeoHom e) x ∈ B :=
  fun x hx => by rw [sphHomeoHom_apply]; exact (hAB x).mp hx

/-- The membership condition transported along the inverse homeomorphism. -/
theorem homeoPairMemSymm {e : X ≃ₜ Y} {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) : ∀ y : Y, y ∈ B → (sphHomeoHom e.symm) y ∈ A :=
  fun y hy => by rw [sphHomeoHom_apply]; exact (homeomorph_symm_mem hAB y).mp hy

/-- The homeomorphism itself and its inverse compose to the identity morphism. -/
theorem sphHomeoHom_comp_symm (e : X ≃ₜ Y) :
    sphHomeoHom e ≫ sphHomeoHom e.symm = 𝟙 X := by
  apply TopCat.hom_ext
  ext x
  exact e.symm_apply_apply x

/-- The inverse homeomorphism and the homeomorphism itself compose to the identity morphism. -/
theorem sphHomeoHom_symm_comp (e : X ≃ₜ Y) :
    sphHomeoHom e.symm ≫ sphHomeoHom e = 𝟙 Y := by
  apply TopCat.hom_ext
  ext x
  exact e.apply_symm_apply x

/-- The two restrictions of a homeomorphism of pairs are mutually inverse. -/
theorem pairRestrict_homeomorph_comp (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB)
      ≫ pairRestrict (sphHomeoHom e.symm) B A (homeoPairMemSymm hAB)
      = 𝟙 (TopCat.of A) := by
  apply TopCat.hom_ext
  ext a
  exact e.symm_apply_apply a.1

/-- The restriction of the inverse homeomorphism, composed with the restriction of the
homeomorphism, is the identity. -/
theorem pairRestrict_homeomorph_comp' (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    pairRestrict (sphHomeoHom e.symm) B A (homeoPairMemSymm hAB)
      ≫ pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB)
      = 𝟙 (TopCat.of B) := by
  apply TopCat.hom_ext
  ext b
  exact e.apply_symm_apply b.1

/-- **A homeomorphism induces an isomorphism of singular chain complexes.** -/
theorem isIso_chainMap_sphHomeoHom (e : X ≃ₜ Y) :
    IsIso (Work.Cohomology.chainMap ℤ X Y (sphHomeoHom e)) :=
  IsIso.mk ⟨Work.Cohomology.chainMap ℤ Y X (sphHomeoHom e.symm), by
    rw [chainMap_comp, sphHomeoHom_comp_symm, chainMap_id], by
    rw [chainMap_comp, sphHomeoHom_symm_comp, chainMap_id]⟩

/-- **The restriction of a homeomorphism of pairs induces an isomorphism of chain complexes.** -/
theorem isIso_chainMap_pairRestrict (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    IsIso (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB))) :=
  IsIso.mk ⟨Work.Cohomology.chainMap ℤ (TopCat.of B) (TopCat.of A)
      (pairRestrict (sphHomeoHom e.symm) B A (homeoPairMemSymm hAB)), by
    rw [chainMap_comp, pairRestrict_homeomorph_comp (A := A) (B := B) e hAB, chainMap_id], by
    rw [chainMap_comp, pairRestrict_homeomorph_comp' (A := A) (B := B) e hAB, chainMap_id]⟩

/-- **A homeomorphism of pairs induces an isomorphism of relative chain complexes.** -/
theorem isIso_relChainsMapOf_homeomorph (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    IsIso (relChainsMapOf (sphHomeoHom e) A B (homeoPairMem hAB)) := by
  haveI hq : IsIso (Work.Cohomology.chainMap ℤ X Y (sphHomeoHom e)) :=
    isIso_chainMap_sphHomeoHom e
  haveI hp : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB))) :=
    isIso_chainMap_pairRestrict e hAB
  exact inferInstanceAs (IsIso (cokernel.map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B)
    (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB)))
    (Work.Cohomology.chainMap ℤ X Y (sphHomeoHom e))
    (inclChains_comp_chainMap (sphHomeoHom e) A B (homeoPairMem hAB))))

/-- **A homeomorphism of pairs induces an isomorphism of relative homology groups.** -/
theorem nonempty_relChains_homology_iso_of_homeomorph (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Nonempty ((Work.Cohomology.relChains X A).homology n ≅
      (Work.Cohomology.relChains Y B).homology n) := by
  haveI := isIso_relChainsMapOf_homeomorph e A B hAB
  exact ⟨asIso (HomologicalComplex.homologyMap
    (relChainsMapOf (sphHomeoHom e) A B (homeoPairMem hAB)) n)⟩

end

end Work.StemsB
