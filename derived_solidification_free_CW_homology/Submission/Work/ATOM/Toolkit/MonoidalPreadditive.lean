import Mathlib
import Submission.Work.ATOM.Defs

/-!
# Tensoring is additive in a braided monoidal closed preadditive category

In a braided monoidal closed preadditive category, the tensor product is additive in each variable.
For the first variable this is the statement that the functor `tensorLeft X = X ⊗ -` is a left
adjoint (`ihom.adjunction`), hence additive; for the second variable one transports the statement
across the braiding, which conjugates `- ▷ X` with `X ◁ -`.

The instance `Work.ATOM.Toolkit.instMonoidalPreadditive` is what makes `f ▷ X` and `X ◁ f`
commute with sums and differences in `LightCondAb`, which is needed to move `(1 - S) ⊗ id` past the
tensor comparison isomorphism `ℤ[X] ⊗ ℤ[Y] ≅ ℤ[X × Y]`.

Main results:
* `Work.ATOM.Toolkit.braiding_conj`: `f ▷ Z` is the braiding-conjugate of `Z ◁ f`;
* `Work.ATOM.Toolkit.monoidalPreadditive_of_monoidalClosed`: `MonoidalPreadditive C`;
* `Work.ATOM.Toolkit.instMonoidalPreadditive`: the instance for light condensed abelian groups.
-/

open CategoryTheory Limits MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ATOM.Toolkit

/-- The braiding conjugates whiskering on the right with whiskering on the left:
`f ▷ Z = (β_ _ Z).hom ≫ (Z ◁ f) ≫ (β_ _ Z).inv`. -/
lemma braiding_conj {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z = ((β_ X Z).hom ≫ (Z ◁ f)) ≫ (β_ Y Z).inv := by
  rw [← BraidedCategory.braiding_naturality_left f Z, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Tensoring is additive in a braided monoidal closed preadditive category.**  The functor
`- ⊗ A` is a left adjoint (up to the braiding, `- ⊗ A ≅ A ⊗ -`), hence additive. -/
instance monoidalPreadditive_of_monoidalClosed {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [HasBinaryBiproducts C] :
    MonoidalPreadditive C := by
  have hleft : ∀ A : C, (tensorLeft A).Additive := by
    intro A
    have h : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
      (ihom.adjunction A).leftAdjoint_preservesColimits
    have h2 : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft A) :=
      h.preservesColimitsOfShape
    have h3 : PreservesBinaryBiproducts (tensorLeft A) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  refine { whiskerLeft_zero := ?_, zero_whiskerRight := ?_, whiskerLeft_add := ?_,
           add_whiskerRight := ?_ }
  · intro A B D
    haveI := hleft A
    exact Functor.map_zero (tensorLeft A) B D
  · intro W X Y
    haveI := hleft W
    have hz : W ◁ (0 : X ⟶ Y) = 0 := Functor.map_zero (tensorLeft W) X Y
    rw [braiding_conj (0 : X ⟶ Y) W, hz]
    simp
  · intro A B D f g
    haveI := hleft A
    exact Functor.map_add (tensorLeft A) (f := f) (g := g)
  · intro W X Y f g
    haveI := hleft W
    have hLA : W ◁ (f + g) = W ◁ f + W ◁ g :=
      Functor.map_add (tensorLeft W) (f := f) (g := g)
    calc (f + g) ▷ W
        = ((β_ X W).hom ≫ (W ◁ (f + g))) ≫ (β_ Y W).inv := braiding_conj (f + g) W
      _ = ((β_ X W).hom ≫ (W ◁ f + W ◁ g)) ≫ (β_ Y W).inv := by rw [hLA]
      _ = (((β_ X W).hom ≫ (W ◁ f)) + ((β_ X W).hom ≫ (W ◁ g))) ≫ (β_ Y W).inv := by
            rw [Preadditive.comp_add]
      _ = (((β_ X W).hom ≫ (W ◁ f)) ≫ (β_ Y W).inv) +
            (((β_ X W).hom ≫ (W ◁ g)) ≫ (β_ Y W).inv) := by rw [Preadditive.add_comp]
      _ = f ▷ W + g ▷ W := by rw [braiding_conj f W, braiding_conj g W]

/-- The instance for light condensed abelian groups. -/
instance instMonoidalPreadditive : MonoidalPreadditive LightCondAb :=
  monoidalPreadditive_of_monoidalClosed

/-- Whiskering on the right commutes with subtraction in `LightCondAb`. -/
theorem whiskerRight_sub {X Y Z : LightCondAb} (f g : X ⟶ Y) :
    (f - g) ▷ Z = (f ▷ Z) - (g ▷ Z) :=
  Functor.map_sub (tensorRight Z) (f := f) (g := g)

/-- Whiskering on the left commutes with subtraction in `LightCondAb`. -/
theorem whiskerLeft_sub {X Y Z : LightCondAb} (f g : Y ⟶ Z) :
    X ◁ (f - g) = (X ◁ f) - (X ◁ g) :=
  Functor.map_sub (tensorLeft X) (f := f) (g := g)

end Work.ATOM.Toolkit
