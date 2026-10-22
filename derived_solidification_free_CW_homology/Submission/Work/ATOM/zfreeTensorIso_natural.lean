import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

/-- Naturality of `μ : ℤ[X] ⊗ ℤ[Y] ≅ ℤ[X × Y]` (`Work.ATOM.zfreeTensorIso`) with respect to
`zmap` in both variables at once.  Needed to transport the explicit maps of the `ATOM` area (which
are written as `zmap`-combinations on `ℤ[(ℕ∪∞) × S]`) to `P ⊗ ℤ[S]`. -/
theorem zfreeTensorIso_natural {X X' Y Y' : LightProfinite.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    MonoidalCategory.whiskerRight (Work.ATOM.zmap f) (Work.ATOM.zfree Y) ≫
        (Work.ATOM.zfreeTensorIso X' Y).hom ≫
        Work.ATOM.zmap (MonoidalCategory.whiskerLeft X' g) =
      MonoidalCategory.whiskerLeft (Work.ATOM.zfree X) (Work.ATOM.zmap g) ≫
        (Work.ATOM.zfreeTensorIso X Y').hom ≫
        Work.ATOM.zmap (MonoidalCategory.whiskerRight f Y') := by
  -- `zfree` is the composite of `lightProfiniteToLightCondSet` with `free ℤ`, and `zmap` is the
  -- action of that composite on morphisms; `zfreeTensorIso` is its tensorator `μ`.
  have hμ : ∀ (A B : LightProfinite.{0}),
      (Work.ATOM.zfreeTensorIso A B).hom
        = Functor.LaxMonoidal.μ (lightProfiniteToLightCondSet ⋙ free ℤ) A B := fun _ _ => rfl
  simp only [hμ]
  -- Naturality of `μ` in the second variable, then in the first.
  rw [← Functor.LaxMonoidal.μ_natural_right (F := lightProfiniteToLightCondSet ⋙ free ℤ) X' g]
  rw [← Functor.LaxMonoidal.μ_natural_left (F := lightProfiniteToLightCondSet ⋙ free ℤ) f Y']
  -- Put everything in the same shape so that the interchange law applies syntactically.
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [← Category.assoc, ← Category.assoc, MonoidalCategory.whisker_exchange]

end Work.ATOM
