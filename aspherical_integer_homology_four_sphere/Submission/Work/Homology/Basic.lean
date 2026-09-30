import Mathlib
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Singular homology toolkit: foundations

Notation and elementary API for the singular chain complex and singular homology
with coefficients in an object `R` of `ModuleCat ℤ`, together with the relative
chain complex of a pair `(X, A)`.

The problem's `LeanEval.Topology.intHomology k X` is definitionally the `k`-th
homology of `singChain ZMod X`; see `Work.Homology.intHomology_eq`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-! ## The coefficient ring and the bridge to `intHomology` -/

/-- The coefficient object `ℤ`, as an object of `ModuleCat ℤ`. -/
abbrev ZMod : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- `C_*(X; R)`, the singular chain complex of a topological space `X` with
coefficients in `R : ModuleCat ℤ`. -/
abbrev singChain (R : ModuleCat ℤ) (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj R).obj X

/-- `H_k(X; R)`, singular homology with coefficients in `R`. -/
abbrev singHomology (R : ModuleCat ℤ) (k : ℕ) (X : TopCat) : ModuleCat ℤ :=
  (singChain R X).homology k

/-- The bridge to the problem's `intHomology`: `H_k(X; ℤ)` is the `k`-th homology
of the `ℤ`-singular chain complex, by definition. -/
theorem intHomology_eq (k : ℕ) (X : TopCat) :
    LeanEval.Topology.intHomology k X = singHomology ZMod k X := rfl

/-- Functoriality of the singular chain complex in the space. -/
abbrev singChainMap (R : ModuleCat ℤ) {X Y : TopCat} (f : X ⟶ Y) :
    singChain R X ⟶ singChain R Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj R).map f

/-- Functoriality of singular homology in the space. -/
abbrev singHomologyMap (R : ModuleCat ℤ) (k : ℕ) {X Y : TopCat} (f : X ⟶ Y) :
    singHomology R k X ⟶ singHomology R k Y :=
  HomologicalComplex.homologyMap (singChainMap R f) k

theorem singChainMap_id (R : ModuleCat ℤ) (X : TopCat) :
    singChainMap R (𝟙 X) = 𝟙 (singChain R X) :=
  CategoryTheory.Functor.map_id _ X

theorem singChainMap_comp (R : ModuleCat ℤ) {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singChainMap R (f ≫ g) = singChainMap R f ≫ singChainMap R g :=
  CategoryTheory.Functor.map_comp _ f g

@[simp]
theorem singChainMap_id_apply (R : ModuleCat ℤ) (X : TopCat) :
    singChainMap R (𝟙 X) = 𝟙 (singChain R X) :=
  singChainMap_id R X

@[simp]
theorem singChainMap_comp_apply (R : ModuleCat ℤ) {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singChainMap R (f ≫ g) = singChainMap R f ≫ singChainMap R g :=
  singChainMap_comp R f g

@[simp]
theorem singHomologyMap_id (R : ModuleCat ℤ) (k : ℕ) (X : TopCat) :
    singHomologyMap R k (𝟙 X) = 𝟙 (singHomology R k X) := by
  simp only [singHomologyMap, singChainMap_id]
  exact HomologicalComplex.homologyMap_id _ _

@[simp]
theorem singHomologyMap_comp (R : ModuleCat ℤ) (k : ℕ) {X Y Z : TopCat}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    singHomologyMap R k (f ≫ g) = singHomologyMap R k f ≫ singHomologyMap R k g := by
  simp only [singHomologyMap, singChainMap_comp]
  exact HomologicalComplex.homologyMap_comp _ _ _

/-! ## Degreewise monomorphisms of chain complexes -/

/-- A morphism of chain complexes of `ℤ`-modules which is a monomorphism in every
degree is a monomorphism. -/
theorem mono_of_forall_mono_f {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    (h : ∀ n, Mono (φ.f n)) : Mono φ := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T g hg
  apply HomologicalComplex.hom_ext
  intro n
  have hgn : g.f n ≫ φ.f n = 0 := by
    have := congrArg (fun (α : T ⟶ L) => α.f n) hg
    simpa using this
  exact (Preadditive.mono_iff_cancel_zero (φ.f n)).1 (h n) (T.X n) (g.f n) hgn

/-! ## Pairs and relative homology -/

/-- The inclusion of a subspace. -/
def incl {X : TopCat} (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem incl_apply {X : TopCat} (A : Set X) (x : A) : incl A x = (x : X) := rfl

/-- The inclusion of the singular chain complex of a subspace. -/
abbrev inclChain (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    singChain R (TopCat.of A) ⟶ singChain R X :=
  singChainMap R (incl A)

/-- `C_*(X, A; R) := C_*(X;R) / C_*(A;R)`, the relative singular chain complex. -/
abbrev relChain (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (inclChain R X A)

/-- `H_k(X, A; R)`, relative singular homology. -/
abbrev relHomology (R : ModuleCat ℤ) (k : ℕ) (X : TopCat) (A : Set X) : ModuleCat ℤ :=
  (relChain R X A).homology k

/-- The projection `C_*(X) → C_*(X,A)`. -/
abbrev relProj (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    singChain R X ⟶ relChain R X A :=
  cokernel.π (inclChain R X A)

/-- The short complex `0 → C_*(A) → C_*(X) → C_*(X,A) → 0` of the pair `(X, A)`. -/
abbrev pairSeq (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (inclChain R X A) (relProj R X A) (cokernel.condition _)


/-- A continuous map `f : X ⟶ Y` is a homotopy equivalence: it has a homotopy
inverse. -/
def IsHomotopyEquivalence {X Y : TopCat} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
    Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y))


/-! ## Maps of pairs -/

/-- A continuous map of pairs `(X, A) → (Y, B)`. -/
structure PairHom (X Y : TopCat) (A : Set X) (B : Set Y) where
  /-- The underlying continuous map. -/
  hom : X ⟶ Y
  /-- The map sends `A` into `B`. -/
  mapsTo : ∀ x : X, x ∈ A → hom x ∈ B

namespace PairHom

variable {X Y : TopCat} {A : Set X} {B : Set Y} (Φ : PairHom X Y A B)

/-- The restriction of a map of pairs to the subspaces. -/
def sub : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x => ⟨Φ.hom x, Φ.mapsTo x x.2⟩, by continuity⟩

@[simp]
theorem sub_apply (x : A) : (Φ.sub x : Y) = Φ.hom x := rfl

@[simp]
theorem sub_comp_incl : Φ.sub ≫ incl B = incl A ≫ Φ.hom := by
  ext x
  rfl

/-- The identity map of a pair. -/
def id (X : TopCat) (A : Set X) : PairHom X X A A where
  hom := 𝟙 X
  mapsTo := fun x hx => hx

@[simp]
theorem id_hom (X : TopCat) (A : Set X) : (id X A).hom = 𝟙 X := rfl

/-- Composition of maps of pairs. -/
def comp {Z : TopCat} {C : Set Z} (Ψ : PairHom Y Z B C) (Φ : PairHom X Y A B) :
    PairHom X Z A C where
  hom := Φ.hom ≫ Ψ.hom
  mapsTo := fun x hx => Ψ.mapsTo (Φ.hom x) (Φ.mapsTo x hx)

end PairHom


/-- `A` is a deformation retract of `X`: there is a retraction of `X` onto `A`
which is homotopic to the identity of `X`. -/
structure DeformationRetract (X : TopCat) (A : Set X) where
  /-- The retraction. -/
  retract : X ⟶ TopCat.of A
  /-- The retraction fixes `A`. -/
  retract_incl : incl A ≫ retract = 𝟙 (TopCat.of A)
  /-- `A` is homotopic to the identity inside `X`. -/
  homotopy : Nonempty (TopCat.Homotopy (retract ≫ incl A) (𝟙 X))

end

end Work.Homology
