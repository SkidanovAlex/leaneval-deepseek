/-
AREA TOOLKIT — closure properties of solid-equivalences (foundations).

This file sets up the vocabulary of the area `Work.TOOLKIT`.  Everything else in
`Submission/Work/TOOLKIT/` builds on the definitions and lemmas below.

Conventions (identical to `Submission.Blueprint.Interfaces`):

* `Cpx` is the category of cochain complexes of light condensed abelian groups indexed
  cohomologically by `ComplexShape.up ℤ`;
* `KCat` (resp. `DCat`) is the homotopy category (resp. derived category) of `Cpx`;
* `SDCat` is the derived category of cochain complexes of *solid* light condensed abelian
  groups, and `iD := derivedInclusion : SDCat ⥤ DCat` is the exact functor induced by the
  inclusion of solid objects;
* `SolidEquiv f` (from the blueprint) means: for every `N : SDCat`, the precomposition
  `g ↦ f ≫ g` with `f` is a bijection `(Y ⟶ iD.obj N) → (X ⟶ iD.obj N)`.

The contents of this file are purely definitional/formal: they do not use anything beyond
Mathlib and `ChallengeDeps`.
-/
import Submission.Blueprint.Interfaces

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT

open Submission.Blueprint

/-! ## Basic abbreviations -/

/-- The category of cochain complexes of light condensed abelian groups. -/
abbrev Cpx : Type 1 := CochainComplex LightCondAb ℤ

/-- The homotopy category of cochain complexes of light condensed abelian groups. -/
abbrev KCat : Type 1 := HomotopyCategory LightCondAb (ComplexShape.up ℤ)

/-- The derived category of light condensed abelian groups. -/
abbrev DCat : Type 1 := DerivedCategory LightCondAb

/-- The derived category of light solid abelian groups. -/
abbrev SDCat : Type 1 := DerivedCategory Solid

/-- The degreewise inclusion of complexes of solid objects. -/
abbrev iC : CochainComplex Solid ℤ ⥤ Cpx := Submission.Blueprint.ιC

/-- The inclusion `D(Solid) ⥤ D(LightCondAb)` on derived categories. -/
abbrev iD : SDCat ⥤ DCat := derivedInclusion

/-- Precomposition with a fixed morphism, as a function between `Hom` types. -/
def precomp {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (W : C) : (Y ⟶ W) → (X ⟶ W) :=
  fun g => f ≫ g

@[simp]
lemma precomp_apply {C : Type*} [Category C] {X Y W : C} (f : X ⟶ Y) (g : Y ⟶ W) :
    precomp f W g = f ≫ g := rfl

lemma precomp_comp {C : Type*} [Category C] {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    precomp (f ≫ g) W = precomp f W ∘ precomp g W := by
  funext x
  simp only [Function.comp_apply, precomp_apply, Category.assoc]

/-- Precomposition with a fixed morphism, in the target `iD.obj N` where `N` is a complex of
solid objects.  This is the function whose bijectivity defines `SolidEquiv`. -/
def precompD {X Y : DCat} (f : X ⟶ Y) (N : SDCat) : (Y ⟶ iD.obj N) → (X ⟶ iD.obj N) :=
  fun g => f ≫ g

@[simp]
lemma precompD_apply {X Y : DCat} (f : X ⟶ Y) (N : SDCat) (g : Y ⟶ iD.obj N) :
    precompD f N g = f ≫ g := rfl

lemma precompD_comp {X Y Z : DCat} (f : X ⟶ Y) (g : Y ⟶ Z) (N : SDCat) :
    precompD (f ≫ g) N = precompD f N ∘ precompD g N := by
  funext x
  simp only [Function.comp_apply, precompD_apply, Category.assoc]

/-- `SolidEquiv` unfolded: it is bijectivity of precomposition against every object of
`D(Solid)`. -/
theorem solidEquiv_iff {X Y : DCat} (f : X ⟶ Y) :
    SolidEquiv f ↔ ∀ N : SDCat, Function.Bijective (precompD f N) := Iff.rfl

/-- The defining property of a solid-equivalence, in `precompD` form. -/
theorem SolidEquiv.bijective {X Y : DCat} {f : X ⟶ Y} (hf : SolidEquiv f) (N : SDCat) :
    Function.Bijective (precompD f N) := hf N

/-! ## Invariance of `SolidEquiv` in the target

A solid-equivalence is a statement about precomposition into the objects `iD.obj N`; replacing
the target by an isomorphic one does not change it.  This is the form in which the target
actually appears in the long exact sequence (as `iD.obj N⟦m⟧`). -/

/-- Postcomposition with an isomorphism is a bijection on `Hom` sets. -/
lemma bijective_postcomp_iso {C : Type*} [Category C] {A B Z : C} (e : A ≅ B) :
    Function.Bijective (fun u : Z ⟶ A => u ≫ e.hom) :=
  ⟨fun a b h => by simpa using (cancel_mono e.hom).mp h,
    fun v => ⟨v ≫ e.inv, by simp [Category.assoc]⟩⟩

/-- Precomposition with `f` into two isomorphic targets: the two maps are conjugate by the
bijections given by postcomposition with the isomorphism. -/
theorem solidEquiv_target_iso_iff {X Y : DCat} (f : X ⟶ Y) {N N' : SDCat}
    (e : iD.obj N ≅ iD.obj N') :
    Function.Bijective (precompD f N) ↔ Function.Bijective (precompD f N') := by
  have hY := bijective_postcomp_iso (Z := Y) e
  have hY' := bijective_postcomp_iso (Z := Y) e.symm
  have hX := bijective_postcomp_iso (Z := X) e
  have hX' := bijective_postcomp_iso (Z := X) e.symm
  constructor
  · intro h
    have hcomp : precompD f N' = (fun u : X ⟶ iD.obj N => u ≫ e.hom) ∘ precompD f N ∘
        (fun u : Y ⟶ iD.obj N' => u ≫ e.inv) := by
      funext v
      simp only [Function.comp_apply, precompD_apply, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    rw [hcomp]
    exact hX.comp (h.comp hY')
  · intro h
    have hcomp : precompD f N = (fun u : X ⟶ iD.obj N' => u ≫ e.inv) ∘ precompD f N' ∘
        (fun u : Y ⟶ iD.obj N => u ≫ e.hom) := by
      funext v
      simp only [Function.comp_apply, precompD_apply, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [hcomp]
    exact hX'.comp (h.comp hY)

set_option backward.isDefEq.respectTransparency false in
/-! ## The contravariant long exact sequence attached to a distinguished triangle

For a distinguished triangle `T` in `D(LightCondAb)` and an object `W`, the contravariant
long exact sequence reads

`... → Hom(T.obj₃, W⟦k⟧) → Hom(T.obj₂, W⟦k⟧) → Hom(T.obj₁, W⟦k⟧) → Hom(T.obj₃, W⟦k+1⟧) → ...`

where the first two maps are precomposition with `T.mor₂` and `T.mor₁`, and the third is the
connecting homomorphism `conn`.  The exactness properties are proved in
`Submission/Work/TOOLKIT/Les/`.
-/

/-- Precomposition with `T.mor₁`, at the target `W⟦k⟧`. -/
def pre₁ (T : Triangle DCat) (W : DCat) (k : ℤ) : (T.obj₂ ⟶ W⟦k⟧) → (T.obj₁ ⟶ W⟦k⟧) :=
  fun g => T.mor₁ ≫ g

/-- Precomposition with `T.mor₂`, at the target `W⟦k⟧`. -/
def pre₂ (T : Triangle DCat) (W : DCat) (k : ℤ) : (T.obj₃ ⟶ W⟦k⟧) → (T.obj₂ ⟶ W⟦k⟧) :=
  fun g => T.mor₂ ≫ g

@[simp] lemma pre₁_apply (T : Triangle DCat) (W : DCat) (k : ℤ) (g : T.obj₂ ⟶ W⟦k⟧) :
    pre₁ T W k g = T.mor₁ ≫ g := rfl

@[simp] lemma pre₂_apply (T : Triangle DCat) (W : DCat) (k : ℤ) (g : T.obj₃ ⟶ W⟦k⟧) :
    pre₂ T W k g = T.mor₂ ≫ g := rfl

/-- The distinguished triangle in `D(LightCondAb)ᵒᵖ` attached to a distinguished triangle
`T` in `D(LightCondAb)`, obtained by transporting along the anti-equivalence
`triangleOpEquivalence`.  Its objects are `T.obj₃ᵒᵖ`, `T.obj₂ᵒᵖ` and `T.obj₁ᵒᵖ`. -/
noncomputable abbrev opTriangle (T : Triangle DCat) : Triangle DCatᵒᵖ :=
  (Pretriangulated.triangleOpEquivalence DCat).functor.obj (Opposite.op T)

set_option backward.isDefEq.respectTransparency false in
/-- The connecting homomorphism of the contravariant long exact sequence: it maps
`u : T.obj₁ ⟶ W⟦k⟧` to a morphism `T.obj₃ ⟶ W⟦k+1⟧`.  It is the connecting map
`homologySequenceδ` of the homological functor `preadditiveYoneda.obj W` applied to the
triangle `opTriangle T` (whose third object is `T.obj₁ᵒᵖ` and whose first object is
`T.obj₃ᵒᵖ`). -/
noncomputable def conn (T : Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₁ ⟶ W⟦k⟧) → (T.obj₃ ⟶ W⟦k+1⟧) :=
  ⇑((preadditiveYoneda.obj W).homologySequenceδ (opTriangle T) k (k + 1) rfl)

/-! ## The formal closure properties

These are the fields `comp`, `of_comp_left`, `of_comp_right` and `of_iso` of
`Submission.Blueprint.ToolkitProp`; they only use that `SolidEquiv f` is bijectivity of the
precomposition with `f`. -/

/-- Solid-equivalences are closed under composition. -/
theorem solidEquiv_comp {X Y Z : DCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : SolidEquiv f) (hg : SolidEquiv g) : SolidEquiv (f ≫ g) := by
  have h3 : ∀ N : SDCat, Function.Bijective (precompD (f ≫ g) N) := by
    intro N
    rw [precompD_comp]
    exact (hf N).comp (hg N)
  exact h3

/-- Two-out-of-three: if `f` and `f ≫ g` are solid-equivalences, so is `g`. -/
theorem solidEquiv_of_comp_left {X Y Z : DCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : SolidEquiv f) (hfg : SolidEquiv (f ≫ g)) : SolidEquiv g := by
  have h3 : ∀ N : SDCat, Function.Bijective (precompD g N) := by
    intro N
    have h2 : Function.Bijective (precompD (f ≫ g) N) := hfg N
    rw [precompD_comp] at h2
    exact ((hf N).of_comp_iff' (precompD g N)).1 h2
  exact h3

/-- Two-out-of-three: if `g` and `f ≫ g` are solid-equivalences, so is `f`. -/
theorem solidEquiv_of_comp_right {X Y Z : DCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : SolidEquiv g) (hfg : SolidEquiv (f ≫ g)) : SolidEquiv f := by
  have h3 : ∀ N : SDCat, Function.Bijective (precompD f N) := by
    intro N
    have h2 : Function.Bijective (precompD (f ≫ g) N) := hfg N
    rw [precompD_comp] at h2
    exact (Function.Bijective.of_comp_iff (precompD f N) (hg N)).1 h2
  exact h3

/-- Isomorphisms are solid-equivalences. -/
theorem solidEquiv_of_iso {X Y : DCat} (f : X ⟶ Y) (hf : IsIso f) : SolidEquiv f := by
  have h3 : ∀ N : SDCat, Function.Bijective (precompD f N) := by
    intro N
    have := hf
    constructor
    · intro a b hab
      exact (cancel_epi f).1 hab
    · intro y
      exact ⟨inv f ≫ y, by simp⟩
  exact h3

end Work.TOOLKIT
