import Mathlib
import Submission.Work.ANALYTIC.CatAux.Basic

open CategoryTheory MonoidalCategory MonoidalClosed

namespace Work.ANALYTIC.CatAux

universe u v

/-- Currying/associativity/braiding rearrangement of precomposition by `S` in the first tensor
factor, in an arbitrary braided monoidal closed category `C`.  The source objects `P ⊗ (X ⊗ Z)` and
`(P ⊗ Z)` with `X` curried into the target are canonically isomorphic, and the two precomposition
maps correspond under this isomorphism, hence their bijectivity is equivalent.  The two `Prop`s are
defined in `Submission.Work.ANALYTIC.CatAux.Basic` (import it); in the proof you may
`open CategoryTheory MonoidalCategory MonoidalClosed` and then `unfold` them.

Suggested proof: chain four conjugations:
1. `MonoidalClosed.uncurry_natural_left` (uncurrying the target `ihom X`): the map
   `y ↦ (S ▷ Z) ≫ y` on `Hom(P ⊗ Z, ihom X M)` becomes `u ↦ (X ◁ (S ▷ Z)) ≫ u` on
   `Hom(X ⊗ (P ⊗ Z), M)`; use `Work.ANALYTIC.CatAux.bijective_of_conj` with `e := uncurry`
   (inverse `curry`, via `uncurry_curry`, `curry_uncurry`);
2. `MonoidalCategory.associator_naturality (𝟙 X) S (𝟙 Z)` with the iso `α_ X P Z`, rewriting
   `𝟙 X ⊗ₘ S` by `id_tensorHom`, `f ⊗ₘ 𝟙 Z` by `tensorHom_id`, `𝟙 X ⊗ₘ 𝟙 Z` by
   `id_tensorHom` + `whiskerLeft_id`; use `Work.ANALYTIC.CatAux.bijective_precomp_congr`;
3. `BraidedCategory.braiding_naturality_left S X` whiskered by `(· ▷ Z)` via
   `MonoidalCategory.comp_whiskerRight` (`(S ▷ X) ▷ Z ≫ β.hom ▷ Z = β.hom ▷ Z ≫ (X ◁ S) ▷ Z`),
   with the iso `MonoidalCategory.whiskerRightIso (β_ P X) Z`;
4. `MonoidalCategory.associator_naturality S (𝟙 X) (𝟙 Z)` with the iso `α_ P X Z`.
   Steps 3 and 4 are the reverse direction of steps 1 and 2. -/
theorem bijective_tensor_precomp_curry {C : Type u} [CategoryTheory.Category C]
    [CategoryTheory.MonoidalCategory C] [CategoryTheory.BraidedCategory C]
    [CategoryTheory.MonoidalClosed C] (P X M Z : C) (S : P ⟶ P) :
    Work.ANALYTIC.CatAux.TensorPrecompBij P X M Z S ↔
      Work.ANALYTIC.CatAux.CurryPrecompBij P X M Z S := by
  unfold Work.ANALYTIC.CatAux.TensorPrecompBij Work.ANALYTIC.CatAux.CurryPrecompBij
  -- The canonical rearrangement `P ⊗ (X ⊗ Z) ≅ X ⊗ (P ⊗ Z)`: reassociate, braid `P` past `X`,
  -- reassociate back.
  let φ : P ⊗ (X ⊗ Z) ≅ X ⊗ (P ⊗ Z) :=
    (α_ P X Z).symm ≪≫ whiskerRightIso (β_ P X) Z ≪≫ (α_ X P Z)
  have hφ : φ.hom = (α_ P X Z).inv ≫ ((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom := by
    show ((α_ P X Z).symm ≪≫ whiskerRightIso (β_ P X) Z ≪≫ (α_ X P Z)).hom = _
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom]
  -- Naturality of the associator in the first variable (`P`).
  have h1 : (S ▷ (X ⊗ Z)) ≫ (α_ P X Z).inv = (α_ P X Z).inv ≫ (S ▷ X ▷ Z) :=
    associator_inv_naturality_left S X Z
  -- Naturality of the braiding in the first variable, whiskered by `(· ▷ Z)`.
  have h2 : (S ▷ X ▷ Z) ≫ ((β_ P X).hom ▷ Z) = ((β_ P X).hom ▷ Z) ≫ ((X ◁ S) ▷ Z) :=
    calc (S ▷ X ▷ Z) ≫ ((β_ P X).hom ▷ Z)
        = ((S ▷ X) ≫ (β_ P X).hom) ▷ Z := (comp_whiskerRight (S ▷ X) (β_ P X).hom Z).symm
      _ = ((β_ P X).hom ≫ (X ◁ S)) ▷ Z :=
            congrArg (· ▷ Z) (BraidedCategory.braiding_naturality_left S X)
      _ = ((β_ P X).hom ▷ Z) ≫ ((X ◁ S) ▷ Z) := comp_whiskerRight (β_ P X).hom (X ◁ S) Z
  -- Naturality of the associator in the middle variable (`P`).
  have h3 : ((X ◁ S) ▷ Z) ≫ (α_ X P Z).hom = (α_ X P Z).hom ≫ (X ◁ (S ▷ Z)) :=
    associator_naturality_middle X S Z
  -- The two precomposition maps correspond under `φ`.
  have key : (S ▷ (X ⊗ Z)) ≫ φ.hom = φ.hom ≫ (X ◁ (S ▷ Z)) := by
    rw [hφ]
    calc (S ▷ (X ⊗ Z)) ≫ ((α_ P X Z).inv ≫ ((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom)
        = ((S ▷ (X ⊗ Z)) ≫ (α_ P X Z).inv) ≫ (((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom) :=
          (Category.assoc _ _ _).symm
      _ = ((α_ P X Z).inv ≫ (S ▷ X ▷ Z)) ≫ (((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom) :=
          congrArg (fun m => m ≫ (((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom)) h1
      _ = (α_ P X Z).inv ≫ ((S ▷ X ▷ Z) ≫ (((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom)) :=
          Category.assoc _ _ _
      _ = (α_ P X Z).inv ≫ (((S ▷ X ▷ Z) ≫ ((β_ P X).hom ▷ Z)) ≫ (α_ X P Z).hom) :=
          congrArg (fun m => (α_ P X Z).inv ≫ m) (Category.assoc _ _ _).symm
      _ = (α_ P X Z).inv ≫ ((((β_ P X).hom ▷ Z) ≫ ((X ◁ S) ▷ Z)) ≫ (α_ X P Z).hom) :=
          congrArg (fun m => (α_ P X Z).inv ≫ (m ≫ (α_ X P Z).hom)) h2
      _ = (α_ P X Z).inv ≫ (((β_ P X).hom ▷ Z) ≫ (((X ◁ S) ▷ Z) ≫ (α_ X P Z).hom)) :=
          congrArg (fun m => (α_ P X Z).inv ≫ m) (Category.assoc _ _ _)
      _ = (α_ P X Z).inv ≫ (((β_ P X).hom ▷ Z) ≫ ((α_ X P Z).hom ≫ (X ◁ (S ▷ Z)))) :=
          congrArg (fun m => (α_ P X Z).inv ≫ (((β_ P X).hom ▷ Z) ≫ m)) h3
      _ = (α_ P X Z).inv ≫ ((((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom) ≫ (X ◁ (S ▷ Z))) :=
          congrArg (fun m => (α_ P X Z).inv ≫ m) (Category.assoc _ _ _).symm
      _ = ((α_ P X Z).inv ≫ (((β_ P X).hom ▷ Z) ≫ (α_ X P Z).hom)) ≫ (X ◁ (S ▷ Z)) :=
          (Category.assoc _ _ _).symm
  -- Bijectivity of `uncurry` along the adjunction `(X ⊗ ·) ⊣ (X ⟹ ·)`.
  have he : Function.Bijective
      (uncurry : (P ⊗ Z ⟶ (ihom X).obj M) → (X ⊗ (P ⊗ Z) ⟶ M)) :=
    Equiv.bijective (((ihom.adjunction X).homEquiv (P ⊗ Z) M).symm)
  -- Uncurrying turns precomposition by `S ▷ Z` into precomposition by `X ◁ (S ▷ Z)`.
  have hnat : ∀ y : P ⊗ Z ⟶ (ihom X).obj M,
      uncurry ((S ▷ Z) ≫ y) = (X ◁ (S ▷ Z)) ≫ uncurry y :=
    fun y => uncurry_natural_left (S ▷ Z) y
  exact (bijective_precomp_congr φ key).trans (bijective_of_conj uncurry he hnat).symm

end Work.ANALYTIC.CatAux
