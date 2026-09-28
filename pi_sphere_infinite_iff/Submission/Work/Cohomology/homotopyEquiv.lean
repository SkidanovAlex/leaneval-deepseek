import Mathlib
import Submission.Work.Cohomology.homotopyInvariance

/-!
# Homotopy equivalences induce isomorphisms on singular cohomology

If `f : X ⟶ Y` and `g : Y ⟶ X` are homotopy inverse to each other (i.e. `f ≫ g` is homotopic to
`𝟙 X` and `g ≫ f` is homotopic to `𝟙 Y`), then the induced map
`f* : Hⁿ(Y; R) ⟶ Hⁿ(X; R)` on singular cohomology is an isomorphism, with inverse
`g* : Hⁿ(X; R) ⟶ Hⁿ(Y; R)`.

The proof is purely formal once one has functoriality (`singularCohomologyMap_comp`,
`singularCohomologyMap_id`) and homotopy invariance (`Work.Cohomology.homotopyInvariance`):

* `g* ≫ f* = (f ≫ g)* = (𝟙 X)* = 𝟙` — here `f ≫ g : X ⟶ X` so this lives on `Hⁿ(X; R)`;
* `f* ≫ g* = (g ≫ f)* = (𝟙 Y)* = 𝟙` — here `g ≫ f : Y ⟶ Y` so this lives on `Hⁿ(Y; R)`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

theorem homotopyEquiv (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (g : Y ⟶ X)
    (h1 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f g) (CategoryTheory.CategoryStruct.id X))
    (h2 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g f) (CategoryTheory.CategoryStruct.id Y))
    (n : ℕ) : CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap R X Y f n) := by
  refine CategoryTheory.IsIso.mk ⟨singularCohomologyMap R Y X g n, ?_, ?_⟩
  · -- `f* ≫ g* = (g ≫ f)* = (𝟙 Y)* = 𝟙`
    rw [← singularCohomologyMap_comp (R := R) (X := Y) (Y := X) (Z := Y) g f n]
    rw [homotopyInvariance R Y Y h2 n, singularCohomologyMap_id]
  · -- `g* ≫ f* = (f ≫ g)* = (𝟙 X)* = 𝟙`
    rw [← singularCohomologyMap_comp (R := R) (X := X) (Y := Y) (Z := X) f g n]
    rw [homotopyInvariance R X X h1 n, singularCohomologyMap_id]

end

end Work.Cohomology
