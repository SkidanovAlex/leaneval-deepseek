/-
Copyright (c) 2026 The CWIND team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Blueprint.Interfaces

/-!
# CWIND — the natural comparison with singular chains (hole 10)

This file sets up the *definitions* of area CWIND: the simplicial space `n ↦ X^{Δⁿ}` of
continuous maps from the topological `n`-simplex into a space `X` (with the compact-open
topology), the resulting simplicial light condensed abelian group `ℤ[X^{Δ•}]`, and the complex

`A(X) = extend (alternatingFaceMapComplex (n ↦ ℤ[X^{Δⁿ}]))`,

which sits in degrees `≤ 0` and for which the inclusion `ℤ[X] ⟶ A(X)` in degree `0` and the
comparison map `C_sing(X) ⟶ A(X)` (identity from the discrete topology) are the natural zigzag
of REFS/05 §1.

We work with `SimplexCategory.toTop₀` (the un-ulifted topological simplex
`↧(StdSimplex ℝ (Fin (n+1)))`) so that the spaces `Δⁿ` are literally the standard simplices used
to define the singular simplicial set of a topological space (`TopCat.toSSet`).

## Main definitions

* `Work.CWIND.Δ n` — the topological `n`-simplex.
* `Work.CWIND.singSpace X n` — the compact-open space `X^{Δⁿ}`.
* `Work.CWIND.singSpaceObj X` — the singular simplicial space of `X`.
* `Work.CWIND.singSpaceFunctor` — the same, functorially in `X`.
* `Work.CWIND.Y` — the simplicial object `n ↦ ℤ[X^{Δⁿ}]` in light condensed abelian groups.
* `Work.CWIND.YFunctor` — the same, functorially in `X`.
* `Work.CWIND.Achain`, `Work.CWIND.A` — the alternating face map complex of `Y`, and its
  extension to a cochain complex indexed by `ℤ` (concentrated in degrees `≤ 0`).
* `Work.CWIND.a0` — the degree `0` comparison map `ℤ[X] ⟶ A(X)`.
-/

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace Work.CWIND

open Opposite Submission.Blueprint
open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## The simplex and the compact-open mapping spaces -/

/-- The topological `n`-simplex `Δⁿ`. -/
abbrev Δ (n : ℕ) : TopCat.{0} := SimplexCategory.toTop₀.obj ⦋n⦌

/-- The space `X^{Δⁿ}` of continuous maps `Δⁿ ⟶ X`, with the compact-open topology. -/
abbrev singSpace (X : TopCat.{0}) (n : ℕ) : TopCat.{0} := TopCat.of C(Δ n, X)

@[simp]
lemma coe_singSpace (X : TopCat.{0}) (n : ℕ) : (singSpace X n : Type) = C(Δ n, X) := rfl

/-- Evaluation at a point is continuous for the compact-open topology. -/
lemma continuous_evalAt {X : Type*} [TopologicalSpace X] {n : ℕ} (s : Δ n) :
    Continuous fun g : C(Δ n, X) => g s := by
  rw [continuous_def]
  intro U hU
  convert ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_singleton (x := s)) hU using 1
  ext g
  simp

/-- `X^{Δⁿ}` is Hausdorff as soon as `X` is. -/
instance instT2SpaceSingSpace (X : TopCat.{0}) (n : ℕ) [T2Space X] : T2Space (singSpace X n) :=
  T2Space.of_injective_continuous (f := fun (g : C(Δ n, X)) (s : Δ n) => g s)
    (fun _ _ h => ContinuousMap.ext fun s => congrFun h s)
    (continuous_pi fun s => continuous_evalAt s)

/-- The evaluation map `X^{Δⁿ} ⟶ X` at a point `s : Δⁿ`. -/
def evalAt (X : TopCat.{0}) (n : ℕ) (s : Δ n) : singSpace X n ⟶ X :=
  TopCat.ofHom ⟨fun g => g s, continuous_evalAt s⟩

@[simp]
lemma evalAt_apply (X : TopCat.{0}) (n : ℕ) (s : Δ n) (g : singSpace X n) :
    evalAt X n s g = g s := rfl

/-- The constant map `X ⟶ X^{Δⁿ}`. -/
def constMap (X : TopCat.{0}) (n : ℕ) : X ⟶ singSpace X n :=
  TopCat.ofHom (ContinuousMap.const' (X := ↥(Δ n)) (Y := ↥X))

@[simp]
lemma constMap_apply (X : TopCat.{0}) (n : ℕ) (x : X) :
    constMap X n x = ContinuousMap.const (Δ n) x := rfl

@[reassoc (attr := simp)]
lemma constMap_comp_evalAt (X : TopCat.{0}) (n : ℕ) (s : Δ n) :
    constMap X n ≫ evalAt X n s = 𝟙 X := by
  apply TopCat.ext
  intro x
  rfl

/-- The map `X ⟶ Y` induces `X^{Δⁿ} ⟶ Y^{Δⁿ}` by postcomposition. -/
abbrev singSpacePostcomp {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singSpace X n ⟶ singSpace Y n :=
  TopCat.ofHom ⟨fun g => f.hom.comp g, ContinuousMap.continuous_postcomp f.hom⟩

lemma singSpacePostcomp_hom {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (singSpacePostcomp f n).hom = ⟨fun g => f.hom.comp g,
      ContinuousMap.continuous_postcomp f.hom⟩ := rfl

@[simp]
lemma singSpacePostcomp_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (g : singSpace X n) : singSpacePostcomp f n g = f.hom.comp g := rfl

/-! ## The singular simplicial space -/

/-- The simplicial structure map `X^{Δᵐ} ⟶ X^{Δⁿ}` induced by `φ : ⦋m⦌ ⟶ ⦋n⦌`. -/
abbrev singSpaceMap {m n : SimplexCategory} (X : TopCat.{0}) (φ : m ⟶ n) :
    singSpace X n.len ⟶ singSpace X m.len :=
  TopCat.ofHom ⟨fun g => g.comp (SimplexCategory.toTop₀.map φ).hom,
    ContinuousMap.continuous_precomp _⟩

lemma singSpaceMap_hom {m n : SimplexCategory} (X : TopCat.{0}) (φ : m ⟶ n) :
    (singSpaceMap X φ).hom = ⟨fun g => g.comp (SimplexCategory.toTop₀.map φ).hom,
      ContinuousMap.continuous_precomp _⟩ := rfl

@[simp]
lemma singSpaceMap_apply {m n : SimplexCategory} (X : TopCat.{0}) (φ : m ⟶ n)
    (g : singSpace X n.len) :
    singSpaceMap X φ g = g.comp (SimplexCategory.toTop₀.map φ).hom := rfl

/-- The singular simplicial space of `X`, whose `n`-th object is `X^{Δⁿ}`. -/
abbrev singSpaceObj (X : TopCat.{0}) : SimplicialObject TopCat.{0} where
  obj n := singSpace X n.unop.len
  map {m n} φ := singSpaceMap X φ.unop
  map_id n := by
    apply TopCat.ext
    intro g
    simp only [singSpaceMap, ConcreteCategory.hom_ofHom, TopCat.hom_id, unop_id,
      CategoryTheory.Functor.map_id, ContinuousMap.comp_id, ContinuousMap.coe_mk,
      ContinuousMap.id_apply]
  map_comp {m n k} φ ψ := by
    apply TopCat.ext
    intro g
    simp only [singSpaceMap, ConcreteCategory.hom_ofHom, TopCat.hom_comp, unop_comp,
      CategoryTheory.Functor.map_comp, ContinuousMap.comp_assoc, ContinuousMap.coe_mk,
      ContinuousMap.comp_apply]

@[simp]
lemma singSpaceObj_obj (X : TopCat.{0}) (n : SimplexCategoryᵒᵖ) :
    (singSpaceObj X).obj n = singSpace X n.unop.len := rfl

@[simp]
lemma singSpaceObj_map {m n : SimplexCategoryᵒᵖ} (X : TopCat.{0}) (φ : m ⟶ n) :
    (singSpaceObj X).map φ = singSpaceMap X φ.unop := rfl

/-- The singular simplicial space, functorially in the space. -/
abbrev singSpaceFunctor : TopCat.{0} ⥤ SimplicialObject TopCat.{0} where
  obj := singSpaceObj
  map {X Y} f :=
    { app := fun n => singSpacePostcomp f n.unop.len
      naturality {m n} φ := by
        apply TopCat.ext
        intro g
        simp only [singSpaceObj_map, singSpaceMap, singSpacePostcomp, ConcreteCategory.hom_ofHom,
          TopCat.hom_comp, ContinuousMap.comp_assoc, ContinuousMap.coe_mk,
          ContinuousMap.comp_apply] }
  map_id X := by
    ext n : 2
    simp only [singSpacePostcomp, ConcreteCategory.hom_ofHom, TopCat.hom_id, ContinuousMap.comp_apply,
      ContinuousMap.id_apply, NatTrans.id_app, ContinuousMap.id_comp, ContinuousMap.coe_mk]
  map_comp {X Y Z} f g := by
    ext n : 2
    simp only [singSpacePostcomp, ConcreteCategory.hom_ofHom, TopCat.hom_comp, TopCat.comp_app,
      ContinuousMap.comp_apply, NatTrans.comp_app, ContinuousMap.coe_mk,
      ContinuousMap.comp_assoc]

@[simp]
lemma singSpaceFunctor_obj (X : TopCat.{0}) : singSpaceFunctor.obj X = singSpaceObj X := rfl

@[simp]
lemma singSpaceFunctor_map_app (X Y : TopCat.{0}) (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (singSpaceFunctor.map f).app n = singSpacePostcomp f n.unop.len := rfl

@[simp]
lemma singSpaceFunctor_map_app_apply {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (g : singSpace X n.unop.len) :
    (singSpaceFunctor.map f).app n g = f.hom.comp g := rfl

/-! ## The simplicial light condensed abelian group `n ↦ ℤ[X^{Δⁿ}]` -/

/-- The simplicial light condensed abelian group `n ↦ ℤ[X^{Δⁿ}]`. -/
abbrev Y (X : TopCat.{0}) : SimplicialObject LightCondAb :=
  singSpaceObj X ⋙ freeLightCondAbOfTopFunctor

/-- The simplicial light condensed abelian group `n ↦ ℤ[X^{Δⁿ}]`, functorially in `X`. -/
abbrev YFunctor : TopCat.{0} ⥤ SimplicialObject LightCondAb :=
  singSpaceFunctor ⋙ (SimplicialObject.whiskering TopCat.{0} LightCondAb).obj
    freeLightCondAbOfTopFunctor

@[simp]
lemma Y_obj (X : TopCat.{0}) (n : SimplexCategoryᵒᵖ) :
    (Y X).obj n = freeLightCondAbOfTop (singSpace X n.unop.len) := rfl

@[simp]
lemma YFunctor_obj (X : TopCat.{0}) : YFunctor.obj X = Y X := rfl

/-- The `i`-th face map `ℤ[X^{Δⁿ⁺¹}] ⟶ ℤ[X^{Δⁿ}]` of the simplicial object `Y X`. -/
lemma Y_δ_eq (X : TopCat.{0}) {n : ℕ} (i : Fin (n + 2)) :
    (Y X).δ i = freeLightCondAbOfTopFunctor.map (singSpaceMap X (SimplexCategory.δ i)) := rfl

@[simp]
lemma Y_δ_apply (X : TopCat.{0}) {n : ℕ} (i : Fin (n + 2)) :
    (Y X).δ i = freeLightCondAbOfTopFunctor.map (singSpaceMap X (SimplexCategory.δ i)) := rfl

/-! ## The complex `A(X)` -/

/-- The alternating face map complex of `Y X` (a chain complex in degrees `ℕ`). -/
abbrev Achain (X : TopCat.{0}) : ChainComplex LightCondAb ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex LightCondAb).obj (Y X)

/-- The alternating face map complex of `Y`, functorially in `X`. -/
abbrev AchainFunctor : TopCat.{0} ⥤ ChainComplex LightCondAb ℕ :=
  YFunctor ⋙ AlgebraicTopology.alternatingFaceMapComplex LightCondAb

/-- The complex `A(X)`: the alternating face map complex of `n ↦ ℤ[X^{Δⁿ}]`, extended to a
cochain complex indexed by `ℤ` (hence concentrated in degrees `≤ 0`). -/
abbrev A (X : TopCat.{0}) : CochainComplex LightCondAb ℤ :=
  (Achain X).extend ComplexShape.embeddingDownNat

/-- `A`, functorially in `X`. -/
abbrev AFunctor : TopCat.{0} ⥤ CochainComplex LightCondAb ℤ :=
  AchainFunctor ⋙ ComplexShape.embeddingDownNat.extendFunctor LightCondAb

@[simp]
lemma A_eq (X : TopCat.{0}) : A X = AFunctor.obj X := rfl

@[simp]
lemma Achain_X (X : TopCat.{0}) (n : ℕ) : (Achain X).X n = freeLightCondAbOfTop (singSpace X n) :=
  rfl

/-- In non-positive degrees, `A X` is the chain complex `Achain X` reindexed. -/
noncomputable def AXIso (X : TopCat.{0}) (n : ℕ) :
    (A X).X (-(n : ℤ)) ≅ (Achain X).X n :=
  HomologicalComplex.extendXIso _ _ (by simp)

@[reassoc]
lemma A_d_eq (X : TopCat.{0}) (m n : ℕ) :
    (A X).d (-(m : ℤ)) (-(n : ℤ)) =
      (AXIso X m).hom ≫ (Achain X).d m n ≫ (AXIso X n).inv :=
  HomologicalComplex.extend_d_eq _ _ (by simp) (by simp)

/-- `A X` vanishes in positive degrees. -/
lemma isZero_A_X_of_pos (X : TopCat.{0}) {q : ℤ} (hq : 0 < q) : IsZero ((A X).X q) :=
  HomologicalComplex.isZero_extend_X (Achain X) ComplexShape.embeddingDownNat q (by
    intro n hn
    simp only [ComplexShape.embeddingDownNat_f] at hn
    omega)

/-- The degree `0` component `ℤ[X] ⟶ A(X)^0` of the natural comparison map `a`, induced by the
constant map `X ⟶ X^{Δ⁰}`. -/
def a0 (X : TopCat.{0}) : freeLightCondAbOfTop X ⟶ (A X).X 0 :=
  freeLightCondAbOfTopFunctor.map (constMap X 0) ≫ (AXIso X 0).inv

/-! ## The unit interval and the inclusion `Y ⟶ Y × [0,1]` at `1` -/

/-- The projection `Y × [0,1] ⟶ Y`. -/
def prI (Y : TopCat.{0}) : TopCat.of (Y × unitInterval) ⟶ Y :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The inclusion `Y ⟶ Y × [0,1]`, `y ↦ (y, 1)`. -/
def i₁ (Y : TopCat.{0}) : Y ⟶ TopCat.of (Y × unitInterval) :=
  TopCat.ofHom ⟨fun y => (y, 1), by fun_prop⟩

@[reassoc (attr := simp)]
lemma i₀_comp_prI (Y : TopCat.{0}) : Submission.Blueprint.i₀ Y ≫ prI Y = 𝟙 Y := by
  apply TopCat.ext
  intro y
  rfl

@[reassoc (attr := simp)]
lemma i₁_comp_prI (Y : TopCat.{0}) : i₁ Y ≫ prI Y = 𝟙 Y := by
  apply TopCat.ext
  intro y
  rfl

/-! ## The levelwise comparison map `b` (singular chains ⟶ `A`) -/

/-- The `ℕ`-graded chain complex underlying the singular chain complex (before extension). -/
abbrev Csrc (X : TopCat.{0}) : ChainComplex LightCondAb ℕ :=
  (singC ⋙ (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj X

/-- The identification of the extended singular chain complex with its `ℕ`-graded form. -/
noncomputable def CXIso (X : TopCat.{0}) (n : ℕ) :
    (Csrc X).X n ≅ (singularChainsLightCondAbComplexFunctor.obj X).X (-(n : ℤ)) :=
  (HomologicalComplex.extendXIso _ _ (by simp)).symm

/-- The point of the light condensed set `X^{Δⁿ}` corresponding to a singular `n`-simplex. -/
def thePoint (X : TopCat.{0}) (n : ℕ) (x : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    LightCondSet.underlying.obj (topCatToLightCondSet.obj (singSpace X n)) :=
  ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥(singSpace X n))
    (TopCat.toSSetObjEquiv X (op ⦋n⦌) x)

/-- The corresponding element of `Γ(ℤ[X^{Δⁿ}])`, i.e. the generator at that point. -/
def theGen (X : TopCat.{0}) (n : ℕ) (x : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (LightCondensed.underlying (ModuleCat ℤ)).obj (freeLightCondAbOfTop (singSpace X n)) :=
  (LightCondSet.underlying.map ((LightCondensed.freeForgetAdjunction ℤ).unit.app
      (topCatToLightCondSet.obj (singSpace X n)))) (thePoint X n x)

/-- The level-`n` comparison map `ℤ[Singₙ X] ⟶ ℤ[X^{Δⁿ}]`, induced by the identity on
simplices (each singular `n`-simplex is a point of `X^{Δⁿ}`). -/
noncomputable def bLevel (X : TopCat.{0}) (n : ℕ) :
    (LightCondensed.discrete (ModuleCat ℤ)).obj
        (∐ (fun _ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) => ModuleCat.of ℤ ℤ))
      ⟶ freeLightCondAbOfTop (singSpace X n) :=
  (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _ |>.symm
    (Sigma.desc (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (theGen X n x))))

/-! ## The constant simplicial object and the map `a` -/

/-- The extension of the alternating face map complex of the constant simplicial object at
`ℤ[X]`. -/
abbrev Aconst (X : TopCat.{0}) : CochainComplex LightCondAb ℤ :=
  ((AlgebraicTopology.alternatingFaceMapComplex LightCondAb).obj
    ((SimplicialObject.const LightCondAb).obj (freeLightCondAbOfTop X))).extend
      ComplexShape.embeddingDownNat

/-- In non-positive degrees, `Aconst X` is the alternating face map complex of the constant
simplicial object, reindexed. -/
noncomputable def AconstXIso (X : TopCat.{0}) (n : ℕ) :
    (Aconst X).X (-(n : ℤ)) ≅
      ((AlgebraicTopology.alternatingFaceMapComplex LightCondAb).obj
        ((SimplicialObject.const LightCondAb).obj (freeLightCondAbOfTop X))).X n :=
  HomologicalComplex.extendXIso _ _ (by simp)

@[simp]
lemma Aconst_chain_X (X : TopCat.{0}) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex LightCondAb).obj
      ((SimplicialObject.const LightCondAb).obj (freeLightCondAbOfTop X))).X n =
      freeLightCondAbOfTop X := rfl

/-- The class of spaces whose singular chains compute `A` up to solid-equivalence, for a fixed
comparison map `b`. -/
def GOf (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) (X : TopCat.{0}) : Prop :=
  T2Space X ∧ SolidEquiv ((DerivedCategory.Q).map (b.app X))

end Work.CWIND
