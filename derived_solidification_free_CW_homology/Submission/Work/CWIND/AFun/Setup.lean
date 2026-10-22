import Mathlib
import Submission.Work.CWIND.Basic

/-!
# CWIND/T4 — setup: the comparison maps for `ℤ[X] ⟶ A(X)`

Definitions used in the proof of `Work.CWIND.AFun.aNat_solidEquiv`.

* `constMap_singSpaceMap` — the constant map `X ⟶ X^{Δⁿ}` is natural in `n`.
* `constToY X` — the simplicial map `const ℤ[X] ⟶ Y X` whose `n`-th component is the map
  `ℤ[X] ⟶ ℤ[X^{Δⁿ}]` induced by the constant map `X ⟶ X^{Δⁿ}`.
* `AchainConst X` — the alternating face map complex of the constant simplicial object at `ℤ[X]`.
* `Gext X` — the resulting comparison map `Aconst X ⟶ A X`; see `Gext_f_neg`, `Gext_f_zero`.
* `chEquiv X` — Mathlib's homotopy equivalence (from the extra degeneracy of the constant
  simplicial object) between `AchainConst X` and the single complex `(single₀ ℤ[X])`.
* `sE X` — the extension of `(chEquiv X).inv` to cochain complexes, a map
  `(single₀ ℤ[X]).extend ⟶ Aconst X`; see `sE_f_zero`.
* `E' X` — the canonical isomorphism `(single ℤ[X]) ≅ (single₀ ℤ[X]).extend`
  (Mathlib's `extendSingleIso`); see `E'_hom_f_zero`.
* `Ac X` — the comparison map `ℤ[X] ⟶ Aconst X`, defined as `(E' X).hom ≫ sE X`; see `Ac_f_zero`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial

namespace Work.CWIND.AFun

open Work.CWIND

/-- `ℤ[X]` is the object in degree `0` of the single complex on `ℤ[X]` and of its extension:
`ComplexShape.embeddingDownNat.f 0 = 0`. -/
lemma embeddingDownNat_f_zero : ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) := by simp

/-! ## The constant map is natural in the simplex -/

lemma constMap_singSpaceMap (X : TopCat.{0}) {m n : SimplexCategory} (φ : m ⟶ n) :
    constMap X n.len ≫ singSpaceMap X φ = constMap X m.len := by
  apply TopCat.ext
  intro x
  apply ContinuousMap.ext
  intro s
  rfl

/-! ## The simplicial map `const ℤ[X] ⟶ Y X` -/

set_option backward.isDefEq.respectTransparency false in
/-- The simplicial map from the constant simplicial object at `ℤ[X]` to the singular simplicial
space of `X`, whose `n`-th component is induced by the constant map `X ⟶ X^{Δⁿ}`. -/
def constToY (X : TopCat.{0}) :
    (SimplicialObject.const LightCondAb).obj (freeLightCondAbOfTop X) ⟶ Y X where
  app n := freeLightCondAbOfTopFunctor.map (constMap X n.unop.len)
  naturality {m n} φ := by
    rw [show (Y X).map φ = freeLightCondAbOfTopFunctor.map (singSpaceMap X φ.unop) from rfl]
    rw [← Functor.map_comp, constMap_singSpaceMap]
    simp only [Functor.const_obj_map, Functor.const_obj_obj]
    exact Category.id_comp _

@[simp]
lemma constToY_app (X : TopCat.{0}) (n : SimplexCategoryᵒᵖ) :
    (constToY X).app n = freeLightCondAbOfTopFunctor.map (constMap X n.unop.len) := rfl

/-! ## The comparison map `Aconst X ⟶ A X` -/

/-- The alternating face map complex of the constant simplicial object at `ℤ[X]`. -/
abbrev AchainConst (X : TopCat.{0}) : ChainComplex LightCondAb ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex LightCondAb).obj
    ((SimplicialObject.const LightCondAb).obj (freeLightCondAbOfTop X))

/-- The comparison map `Aconst X ⟶ A X`, obtained by applying the alternating face map complex
to `constToY X` and extending to cochain complexes. -/
def Gext (X : TopCat.{0}) : Aconst X ⟶ A X :=
  HomologicalComplex.extendMap
    ((AlgebraicTopology.alternatingFaceMapComplex LightCondAb).map (constToY X))
    ComplexShape.embeddingDownNat

lemma Gext_eq (X : TopCat.{0}) :
    Gext X = HomologicalComplex.extendMap
      ((AlgebraicTopology.alternatingFaceMapComplex LightCondAb).map (constToY X))
      ComplexShape.embeddingDownNat := rfl

/-- The degree `-n` component of the comparison map, in terms of the isomorphisms identifying
the extensions with the chain complexes. -/
lemma Gext_f_neg (X : TopCat.{0}) (n : ℕ) :
    (Gext X).f (-(n : ℤ)) =
      (AconstXIso X n).hom ≫ freeLightCondAbOfTopFunctor.map (constMap X n) ≫
        (AXIso X n).inv := by
  rw [Gext, HomologicalComplex.extendMap_f _ _
    (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) from rfl)]
  rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  rfl

/-- The degree `0` component of the comparison map: it is `a0` transported along `AconstXIso`. -/
lemma Gext_f_zero (X : TopCat.{0}) :
    (Gext X).f 0 = (AconstXIso X 0).hom ≫ a0 X := by
  have h := Gext_f_neg X 0
  simp only [Nat.cast_zero, neg_zero, a0] at h ⊢
  exact h

/-! ## The homotopy equivalence `AchainConst X ≃ (single₀ ℤ[X])` -/

/-- The homotopy equivalence between the alternating face map complex of the constant simplicial
object at `ℤ[X]` and the single complex on `ℤ[X]` (concentrated in degree `0`), coming from the
extra degeneracy of the constant simplicial object. -/
def chEquiv (X : TopCat.{0}) :
    HomotopyEquiv (AchainConst X)
      ((ChainComplex.single₀ LightCondAb).obj (freeLightCondAbOfTop X)) :=
  (SimplicialObject.Augmented.ExtraDegeneracy.const (freeLightCondAbOfTop X)).homotopyEquiv

/-- The `0`-th component of `(chEquiv X).inv` is the identity of `ℤ[X]`. -/
lemma chEquiv_inv_f_zero (X : TopCat.{0}) :
    (chEquiv X).inv.f 0 = 𝟙 (freeLightCondAbOfTop X) := by
  rw [show (chEquiv X).inv =
        (ChainComplex.fromSingle₀Equiv (AchainConst X)
          (freeLightCondAbOfTop X)).symm (𝟙 (freeLightCondAbOfTop X)) from rfl,
    ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]

/-- The `0`-th object of the extension of `(single₀ ℤ[X])`. -/
noncomputable def PEIso (X : TopCat.{0}) :
    (((ChainComplex.single₀ LightCondAb).obj (freeLightCondAbOfTop X)).extend
        ComplexShape.embeddingDownNat).X 0 ≅ freeLightCondAbOfTop X :=
  HomologicalComplex.extendXIso _ _ embeddingDownNat_f_zero

/-- The extension of `(chEquiv X).inv` to cochain complexes. -/
def sE (X : TopCat.{0}) :
    ((ChainComplex.single₀ LightCondAb).obj (freeLightCondAbOfTop X)).extend
        ComplexShape.embeddingDownNat ⟶ Aconst X :=
  HomologicalComplex.extendMap (chEquiv X).inv ComplexShape.embeddingDownNat

/-- The degree `0` component of `sE`. -/
lemma sE_f_zero (X : TopCat.{0}) : (sE X).f 0 =
    (PEIso X).hom ≫ (chEquiv X).inv.f 0 ≫ (AconstXIso X 0).inv := by
  rw [sE, HomologicalComplex.extendMap_f _ _ embeddingDownNat_f_zero]
  rfl

/-- The canonical isomorphism between the single cochain complex on `ℤ[X]` and the extension of
the single chain complex on `ℤ[X]`. -/
def E' (X : TopCat.{0}) :
    (CochainComplex.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X) ≅
      ((ChainComplex.single₀ LightCondAb).obj (freeLightCondAbOfTop X)).extend
        ComplexShape.embeddingDownNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat (freeLightCondAbOfTop X) 0 0
    embeddingDownNat_f_zero).symm

/-- The degree `0` component of `(E' X).hom`. -/
lemma E'_hom_f_zero (X : TopCat.{0}) :
    (E' X).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (freeLightCondAbOfTop X)).hom ≫
        (PEIso X).inv := by
  rw [E', Iso.symm_hom, HomologicalComplex.extendSingleIso_inv_f, ChainComplex.single₀ObjXSelf,
    Iso.refl_inv]
  erw [Category.id_comp]

/-- The comparison map `ℤ[X] ⟶ Aconst X`: the isomorphism `E'` followed by `sE`. -/
def Ac (X : TopCat.{0}) :
    (CochainComplex.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X) ⟶ Aconst X :=
  (E' X).hom ≫ sE X

@[simp]
lemma Ac_eq (X : TopCat.{0}) : Ac X = (E' X).hom ≫ sE X := rfl

/-- The degree `0` component of `Ac`: the identity of `ℤ[X]` followed by the inverse of the
reindexing isomorphism. -/
lemma Ac_f_zero (X : TopCat.{0}) :
    (Ac X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (freeLightCondAbOfTop X)).hom ≫
        (AconstXIso X 0).inv := by
  rw [Ac, HomologicalComplex.comp_f, E'_hom_f_zero, sE_f_zero]
  erw [chEquiv_inv_f_zero]
  rw [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp]

end Work.CWIND.AFun
