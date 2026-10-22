import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.AFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-!
# CWIND/T3 — the natural transformation `a`

This file builds the natural transformation of cochain complexes
`a : freeLightCondAbOfTopFunctor ⋙ CochainComplex.singleFunctor LightCondAb 0 ⟶ AFunctor`
whose degree-`0` component at `X` is `a0 X : ℤ[X] ⟶ A(X)^0`, the map induced by the constant map
`X ⟶ X^{Δ⁰}` (see `Basic.lean` and REFS/05 §1).  Since `A(X)` is concentrated in degrees `≤ 0`,
such a chain map is determined by its degree-`0` component, and the chain-map condition is
automatic; the only content is naturality in the space `X`.

## Implementation notes

The map `a0 X` of `Basic.lean` is typed with the *object* `freeLightCondAbOfTop X` as its source,
whereas the sources appearing in a naturality square are the objects `freeLightCondAbOfTopFunctor.obj X`
of the functor `freeLightCondAbOfTopFunctor`.  These two expressions denote the same object of
`LightCondAb` only up to unfolding a semireducible definition, which makes the goals of the
naturality proof ill-typed at the reducible transparency used by `rw`.  We therefore introduce a
"clean" copy `a0F X` of `a0 X`, defined with `eqToHom` and a degree-`0` copy `AXIso0 X` of the
canonical iso `AXIso X 0` of `Basic.lean`; the two agree by `a0F_eq_a0`, and all composites used
below are syntactically well typed. -/

noncomputable section

/-- The canonical isomorphism `A(X)^0 ≅ Achain(X)^0`, in the form `AFunctor.obj X` (rather than
`A X`) so that its composites with the maps appearing in `AFunctor.map` are syntactically well
typed.  It agrees with `AXIso X 0` of `Basic.lean`. -/
noncomputable def AXIso0 (X : TopCat.{0}) : (AFunctor.obj X).X 0 ≅ (Achain X).X 0 :=
  HomologicalComplex.extendXIso (Achain X) ComplexShape.embeddingDownNat (by simp)

/-- A copy of `a0 X` whose source is displayed as `freeLightCondAbOfTopFunctor.obj X`; it is
equal to `a0 X` (`a0F_eq_a0`). -/
noncomputable def a0F (X : TopCat.{0}) : freeLightCondAbOfTopFunctor.obj X ⟶ (AFunctor.obj X).X 0 :=
  freeLightCondAbOfTopFunctor.map (constMap X 0) ≫
    eqToHom (by rfl : freeLightCondAbOfTopFunctor.obj (singSpace X 0) = (Achain X).X 0) ≫
    (AXIso0 X).inv

lemma a0F_eq_a0 (X : TopCat.{0}) : a0F X = a0 X := by
  simp only [a0F, a0, eqToHom_refl, Category.id_comp]
  exact congrArg (fun (e : (AFunctor.obj X).X 0 ≅ (Achain X).X 0) =>
    freeLightCondAbOfTopFunctor.map (constMap X 0) ≫ e.inv)
    (show AXIso0 X = AXIso X 0 from rfl)

/-- Naturality of the constant map: the square comparing the constant maps `X ⟶ X^{Δⁿ}` and
`Y ⟶ Y^{Δⁿ}` commutes. -/
lemma constMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    constMap X n ≫ singSpacePostcomp f n = f ≫ constMap Y n := by
  apply TopCat.ext
  intro x
  ext s
  rfl

/-- The key elementary computation behind naturality of `a0`: the two ways of going from
`ℤ[X^{Δ⁰}]` to `ℤ[Y^{Δ⁰}]` (via `f` on the outside or via `singSpacePostcomp f 0` on the inside)
agree. -/
lemma step {X Y : TopCat.{0}} (f : X ⟶ Y) :
    freeLightCondAbOfTopFunctor.map f ≫ freeLightCondAbOfTopFunctor.map (constMap Y 0) =
      freeLightCondAbOfTopFunctor.map (constMap X 0) ≫
        freeLightCondAbOfTopFunctor.map (singSpacePostcomp f 0) := by
  rw [← freeLightCondAbOfTopFunctor.map_comp, ← freeLightCondAbOfTopFunctor.map_comp,
      constMap_naturality]

/-- The defining property of `a0 X`, in a form where the canonical isomorphism `AXIso X 0` is
cancelled. -/
lemma a0_eq_comp (X : TopCat.{0}) :
    a0 X ≫ (AXIso X 0).hom = freeLightCondAbOfTopFunctor.map (constMap X 0) := by
  unfold a0
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The degree-`0` component of `AFunctor.map f`, transported along the canonical isomorphisms
`AXIso`. -/
lemma A_map_f_zero {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (AFunctor.map f).f 0 =
      (AXIso X 0).hom ≫ (AchainFunctor.map f).f 0 ≫ (AXIso Y 0).inv := by
  change (HomologicalComplex.extendMap (AchainFunctor.map f) ComplexShape.embeddingDownNat).f (0:ℤ) =
      (AXIso X 0).hom ≫ (AchainFunctor.map f).f 0 ≫ (AXIso Y 0).inv
  rw [HomologicalComplex.extendMap_f (i := 0) (i' := (0:ℤ)) (h := by simp)]
  congr 2

/-- The degree-`0` component of `AchainFunctor.map f`, i.e. the map induced by
`singSpacePostcomp f 0`. -/
lemma Achain_map_f_zero {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (AchainFunctor.map f).f 0 = freeLightCondAbOfTopFunctor.map (singSpacePostcomp f 0) := rfl

/-- Naturality of `a0` in the space. -/
lemma a0_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    freeLightCondAbOfTopFunctor.map f ≫ a0 Y = a0 X ≫ (AFunctor.map f).f 0 := by
  unfold a0
  rw [A_map_f_zero f]
  erw [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Achain_map_f_zero f]
  conv_rhs => erw [← Category.assoc]
  conv_lhs => erw [← Category.assoc]
  exact congrArg (fun g => g ≫ (AXIso Y 0).inv) (step f)

/-- Naturality of the "clean" copy `a0F` of `a0`. -/
lemma a0F_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    freeLightCondAbOfTopFunctor.map f ≫ a0F Y = a0F X ≫ (AFunctor.map f).f 0 := by
  rw [a0F_eq_a0 Y, a0F_eq_a0 X]
  exact a0_naturality f

/-- The degree-`0` component of the map `a`: the chain map out of the single complex concentrated
in degree `0` determined by `a0F`. -/
noncomputable def aMap (X : TopCat.{0}) :
    (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj
        (freeLightCondAbOfTopFunctor.obj X) ⟶ AFunctor.obj X :=
  HomologicalComplex.mkHomFromSingle (A := freeLightCondAbOfTopFunctor.obj X) (a0F X)
    (fun k hk => by
      rw [ComplexShape.up_Rel] at hk
      exact (isZero_A_X_of_pos X (by omega : 0 < k)).eq_of_tgt _ _)

lemma aMap_f_zero (X : TopCat.{0}) :
    (aMap X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (freeLightCondAbOfTopFunctor.obj X)).hom ≫ a0F X :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- Naturality of `aMap` in the space. -/
lemma aMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map
        (freeLightCondAbOfTopFunctor.map f) ≫ aMap Y
      = aMap X ≫ AFunctor.map f := by
  apply HomologicalComplex.from_single_hom_ext
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  rw [HomologicalComplex.single_map_f_self, aMap_f_zero X, aMap_f_zero Y]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun g => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (freeLightCondAbOfTopFunctor.obj X)).hom ≫ g) (a0F_naturality f)

/-- **CWIND/T3. The map `a`.**  Build the natural transformation of cochain complexes
`a : freeLightCondAbOfTopFunctor ⋙ CochainComplex.singleFunctor LightCondAb 0 ⟶ AFunctor`, where
`singleFunctor LightCondAb 0` is the single-object complex concentrated in degree `0` and
`A(X) = extend (alternatingFaceMapComplex (n ↦ ℤ[X^{Δⁿ}]))` is the mapping-space complex of
`Basic.lean`.  Since `A(X)` is concentrated in degrees `≤ 0`, a morphism out of the single complex
in degree `0` is uniquely determined by its degree-`0` component, which is required here to be
`a0 X : ℤ[X] ⟶ A(X)^0 ≅ ℤ[X^{Δ⁰}]`, the map induced by the constant map `X ⟶ X^{Δ⁰}` (the degree-`0`
part of the natural zigzag `ℤ[X] → A(X) ← C_sing(X)` of REFS/05 §1).

The only content is the naturality of this family in `X`; the chain-map condition at degree `0` is
automatic because `A(X)` is concentrated in degrees `≤ 0`. -/
theorem exists_aNat :
    ∃ (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor),
      ∀ (X : TopCat.{0}),
        (a.app X).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (freeLightCondAbOfTop X)).hom ≫
            a0 X := by
  refine ⟨{ app := aMap, naturality := fun {X Y} f => aMap_naturality f }, fun X => ?_⟩
  exact (aMap_f_zero X).trans (congrArg (fun g =>
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (freeLightCondAbOfTopFunctor.obj X)).hom ≫ g) (a0F_eq_a0 X))

end

end Work.CWIND.AFun
