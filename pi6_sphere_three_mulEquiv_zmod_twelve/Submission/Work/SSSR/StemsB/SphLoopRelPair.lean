import Mathlib
import Submission.Work.SSSR.Cohomology.HomologyPairSequence
import Submission.Work.StemsB.RelChainsR
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.StemsB
variable {R : Type} [CommRing R] [Nontrivial R]

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
namespace Work.SSSR.StemsB

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
    pairRestrict f A B hf ≫ Work.SSSR.Cohomology.subtypeIncl Y B
      = Work.SSSR.Cohomology.subtypeIncl X A ≫ f := by
  apply TopCat.hom_ext
  ext a
  rfl

/-- The square relating the inclusions of chains with the chain maps induced by a map of pairs
commutes. -/
theorem inclChains_comp_chainMap (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    Work.SSSR.Cohomology.inclChains R X A ≫ Work.SSSR.Cohomology.chainMap R X Y f
      = Work.SSSR.Cohomology.chainMap R (TopCat.of A) (TopCat.of B) (pairRestrict f A B hf)
        ≫ Work.SSSR.Cohomology.inclChains R Y B := by
  have h := pairRestrict_comp_subtypeIncl f A B hf
  simp only [Work.SSSR.Cohomology.inclChains, Work.SSSR.Cohomology.chainMap]
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- **The induced map on relative singular chains of a map of pairs.** -/
def relChainsMapOf (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (A : Set X) (B : Set Y) (hf : ∀ x : X, x ∈ A → f x ∈ B) :
    Work.SSSR.Cohomology.relChains R X A ⟶ Work.SSSR.Cohomology.relChains R Y B :=
  cokernel.map (Work.SSSR.Cohomology.inclChains R X A) (Work.SSSR.Cohomology.inclChains R Y B)
    (Work.SSSR.Cohomology.chainMap R (TopCat.of A) (TopCat.of B) (pairRestrict f A B hf))
    (Work.SSSR.Cohomology.chainMap R X Y f) (inclChains_comp_chainMap f A B hf)

end

end Work.SSSR.StemsB

namespace Work.SSSR.StemsB

noncomputable section

variable {X Y Z : TopCat}

/-- Composition of the chain maps induced by continuous maps. -/
theorem chainMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.SSSR.Cohomology.chainMap R X Y f ≫ Work.SSSR.Cohomology.chainMap R Y Z g
      = Work.SSSR.Cohomology.chainMap R X Z (f ≫ g) :=
  (Functor.map_comp _ f g).symm

/-- The chain map induced by the identity is the identity. -/
theorem chainMap_id :
    Work.SSSR.Cohomology.chainMap R X X (𝟙 X) = 𝟙 (Work.SSSR.Cohomology.singularChains R X) :=
  show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)).map (𝟙 X) = 𝟙 _ from CategoryTheory.Functor.map_id _ X

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
    IsIso (Work.SSSR.Cohomology.chainMap R X Y (sphHomeoHom e)) :=
  IsIso.mk ⟨Work.SSSR.Cohomology.chainMap R Y X (sphHomeoHom e.symm), by
    rw [chainMap_comp, sphHomeoHom_comp_symm, chainMap_id], by
    rw [chainMap_comp, sphHomeoHom_symm_comp, chainMap_id]⟩

/-- **The restriction of a homeomorphism of pairs induces an isomorphism of chain complexes.** -/
theorem isIso_chainMap_pairRestrict (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    IsIso (Work.SSSR.Cohomology.chainMap R (TopCat.of A) (TopCat.of B)
      (pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB))) :=
  IsIso.mk ⟨Work.SSSR.Cohomology.chainMap R (TopCat.of B) (TopCat.of A)
      (pairRestrict (sphHomeoHom e.symm) B A (homeoPairMemSymm hAB)), by
    rw [chainMap_comp, pairRestrict_homeomorph_comp (A := A) (B := B) e hAB, chainMap_id], by
    rw [chainMap_comp, pairRestrict_homeomorph_comp' (A := A) (B := B) e hAB, chainMap_id]⟩

/-- **A homeomorphism of pairs induces an isomorphism of relative chain complexes.** -/
theorem isIso_relChainsMapOf_homeomorph (R : Type) [CommRing R] [Nontrivial R] (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) :
    IsIso (relChainsMapOf R (sphHomeoHom e) A B (homeoPairMem hAB)) := by
  haveI hq : IsIso (Work.SSSR.Cohomology.chainMap R X Y (sphHomeoHom e)) :=
    isIso_chainMap_sphHomeoHom e
  haveI hp : IsIso (Work.SSSR.Cohomology.chainMap R (TopCat.of A) (TopCat.of B)
      (pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB))) :=
    isIso_chainMap_pairRestrict e hAB
  exact inferInstanceAs (IsIso (cokernel.map (Work.SSSR.Cohomology.inclChains R X A)
    (Work.SSSR.Cohomology.inclChains R Y B)
    (Work.SSSR.Cohomology.chainMap R (TopCat.of A) (TopCat.of B)
      (pairRestrict (sphHomeoHom e) A B (homeoPairMem hAB)))
    (Work.SSSR.Cohomology.chainMap R X Y (sphHomeoHom e))
    (inclChains_comp_chainMap (sphHomeoHom e) A B (homeoPairMem hAB))))

/-- **A homeomorphism of pairs induces an isomorphism of relative homology groups.** -/
theorem nonempty_relChains_homology_iso_of_homeomorph (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Nonempty ((Work.SSSR.Cohomology.relChains R X A).homology n ≅
      (Work.SSSR.Cohomology.relChains R Y B).homology n) := by
  haveI := isIso_relChainsMapOf_homeomorph R e A B hAB
  exact ⟨asIso (HomologicalComplex.homologyMap
    (relChainsMapOf R (sphHomeoHom e) A B (homeoPairMem hAB)) n)⟩

end

end Work.SSSR.StemsB
