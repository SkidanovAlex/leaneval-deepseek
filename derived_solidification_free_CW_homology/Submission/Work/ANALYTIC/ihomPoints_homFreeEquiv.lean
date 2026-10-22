import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.projective_P

namespace Work.ANALYTIC

/-!
# Evaluating the points of an internal hom

`LightCondensed.ihomPoints ℤ A B S` is (up to composition with `uncurry`) the section bijection
`Hom(ℤ[S], A ⟹ B) ≃ (A ⊗ ℤ[S] ⟶ B)`; `Work.ATOM.homFreeEquiv S B` is the section bijection
`Hom(ℤ[S], B) ≃ B(S)`.  The lemma below is the resulting "evaluation commutes with uncurrying"
computation, obtained purely from the two definitions and the naturality of `homFreeEquiv` in the
target (`Work.ATOM.homFreeEquiv_naturality_target`).
-/

open CategoryTheory MonoidalClosed Opposite

/-- **The points of an internal hom, via `homFreeEquiv`.**  Applying `ihomPoints` to a general
element of `((A ⟹ B)(S))` is the same as first transporting that element back to a morphism
`ℤ[S] ⟶ (A ⟹ B)` through the section bijection `Work.ATOM.homFreeEquiv` and then uncurrying.

This is the definitional unfolding `LightCondensed.ihomPoints_apply` together with the definition
of `Work.ATOM.homFreeEquiv`. -/
theorem ihomPoints_homFreeEquiv_apply (A B : LightCondAb) (S : LightProfinite.{0})
    (x : ↥(((CategoryTheory.ihom A).obj B).obj.obj (Opposite.op S))) :
    LightCondensed.ihomPoints ℤ A B S x
      = CategoryTheory.MonoidalClosed.uncurry
          ((Work.ATOM.homFreeEquiv S ((CategoryTheory.ihom A).obj B)).symm x) := by
  rw [LightCondensed.ihomPoints_apply]
  rfl

/-- **Evaluation of the points of an internal hom.**  For a morphism `u : X ⟶ (A ⟹ M)`, a light
profinite set `S` and a morphism `g : ℤ[S] ⟶ X`, the `S`-point of `u` at the section classified by
`g` (under `Work.ATOM.homFreeEquiv`) is classified by the uncurrying of `g` composed with `u`. -/
theorem ihomPoints_homFreeEquiv (A M X : LightCondAb) (u : X ⟶ (CategoryTheory.ihom A).obj M)
    (S : LightProfinite.{0}) (g : Work.ATOM.zfree S ⟶ X) :
    LightCondensed.ihomPoints ℤ A M S
        (u.hom.app (Opposite.op S) (Work.ATOM.homFreeEquiv S X g))
      = CategoryTheory.MonoidalClosed.uncurry (CategoryTheory.CategoryStruct.comp g u) := by
  -- `homFreeEquiv_naturality_target` identifies `u` applied to the section of `g` with the
  -- section of `g ≫ u`, and `ihomPoints_homFreeEquiv_apply` evaluates at that section.
  rw [← Work.ATOM.homFreeEquiv_naturality_target S u g, ihomPoints_homFreeEquiv_apply]
  exact congrArg CategoryTheory.MonoidalClosed.uncurry (Equiv.symm_apply_apply _ _)

end Work.ANALYTIC
