import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.exists_segre_product_u

/-!
# Chow's lemma: the empty case (universe-general)

Universe-general companion of `Work.DSG2.chow_of_isEmpty`.  If `X` is a scheme with empty
underlying space then `X` is the initial object of the category of schemes
(`AlgebraicGeometry.isInitialOfIsEmpty`), so we may take `X' = X` and `g = 𝟙 X`.

* `g = 𝟙 X` is surjective;
* `X` being empty, every morphism out of it is a closed immersion, so any
  `i : X ⟶ ℙ⁰_A` is a closed immersion and initiality gives `i ≫ (ℙ⁰_A → Spec A) = f`,
  which is exactly the factorization required by `DSMap.IsProjOver A f`;
* `IsClosedImmersion.isProper` together with `ℙ⁰_A → Spec A` proper
  (`Work.DSG2.SegreProductU.isProper_pspace_toSpec`) makes `𝟙 X ≫ f` proper.

No hypothesis on `A` is needed.
-/

open CategoryTheory AlgebraicGeometry Limits

-- The `haveI` below really does need to register a typeclass instance, so the style linter's
-- suggestion to use `have` (which only applies to proof-irrelevant data) is not appropriate.
set_option linter.style.haveILetI false

namespace Work.DSG2

/-- **Chow's lemma, empty case, universe-general.**  If `X` is empty then `X` itself
dominates `X` over `Spec A` by a surjective, proper and `A`-projective morphism. -/
theorem chow_of_isEmpty_u (A : Type*) [CommRing A] (X : AlgebraicGeometry.Scheme)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [IsEmpty X] :
    ∃ (X' : AlgebraicGeometry.Scheme) (g : X' ⟶ X),
      Function.Surjective g ∧
        AlgebraicGeometry.IsProper (CategoryTheory.CategoryStruct.comp g f) ∧
          DSMap.IsProjOver A (CategoryTheory.CategoryStruct.comp g f) := by
  -- The empty scheme is initial, so there is a unique morphism out of it.
  have hinit : IsInitial X := isInitialOfIsEmpty
  -- Pick *any* morphism of `X` into `ℙ⁰_A`; it is a closed immersion, and it is *the*
  -- morphism `X ⟶ ℙ⁰_A`, so it certainly makes the square commute.
  let i : X ⟶ DSMap.PSpace A 0 := hinit.to _
  have hci : IsClosedImmersion i := inferInstance
  have hfac : i ≫ DSMap.PSpace.toSpec A 0 = f := hinit.hom_ext _ f
  -- `ℙ⁰_A → Spec A` is proper (universe-general Segre-product file).
  haveI : IsProper (DSMap.PSpace.toSpec A 0) := SegreProductU.isProper_pspace_toSpec A 0
  -- A closed immersion is proper and properness is stable under composition.
  have hproper : IsProper (𝟙 X ≫ f) := by
    rw [show (𝟙 X ≫ f) = i ≫ DSMap.PSpace.toSpec A 0 by
      rw [← hfac, Category.id_comp]]
    infer_instance
  refine ⟨X, 𝟙 X, fun x => ⟨x, rfl⟩, hproper, 0, i, hci, ?_⟩
  -- `IsProjOver A (𝟙 X ≫ f)`: the closed immersion `i` into `ℙ⁰_A` factors it.
  rw [Category.id_comp]
  exact hfac

end Work.DSG2
