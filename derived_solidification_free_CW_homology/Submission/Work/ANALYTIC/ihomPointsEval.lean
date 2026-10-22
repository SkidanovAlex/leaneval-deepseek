import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup

/-!
# AREA ANALYTIC — evaluation of the points of an internal hom

This file proves `Work.ANALYTIC.IhomPointsEval`: for `u : X ⟶ (A ⟹ M)`, a light profinite set `S`
and a morphism `g : ℤ[S] ⟶ X`, the `S`-point of `u` at the section classified by `g` is the
uncurrying of the composite `g ≫ u`:

`ihomPoints ℤ A M S (u.app S (homFreeEquiv S X g)) = uncurry (g ≫ u)`.

The two inputs are:

* `ihomPoints_eq_uncurry`: `ihomPoints` is, by definition, the uncurrying of the inverse of
  `homFreeEquiv` (both are built from the free-forget adjunction, Yoneda and the internal-hom
  adjunction, so their `symm`'s agree definitionally);
* `Work.ATOM.homFreeEquiv_naturality_target`: naturality of `homFreeEquiv` in the target, i.e.
  `homFreeEquiv S (A ⟹ M) (g ≫ u) = u.app S (homFreeEquiv S X g)`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-- `ihomPoints` is the uncurrying of the inverse of `homFreeEquiv`.  Both equivalences are
`(freeForgetAdjunction ℤ).homEquiv` followed by Yoneda, so the identity is a definitional
computation: `ihomPoints R A B S = uncurry ∘ (homFreeEquiv S (A ⟹ B)).symm`. -/
lemma ihomPoints_eq_uncurry (A M : LightCondAb) (S : LightProfinite.{0})
    (x : ↥(((ihom A).obj M).obj.obj (op S))) :
    LightCondensed.ihomPoints ℤ A M S x
      = MonoidalClosed.uncurry ((Work.ATOM.homFreeEquiv S ((ihom A).obj M)).symm x) := by
  rw [LightCondensed.ihomPoints_apply]
  congr 1

/-- **The evaluation of the points of an internal hom.**  The `S`-point of `u : X ⟶ (A ⟹ M)` at
the section `homFreeEquiv S X g` classified by `g : ℤ[S] ⟶ X` is the uncurrying of `g ≫ u`. -/
theorem ihomPointsEval : Work.ANALYTIC.IhomPointsEval := by
  intro A M X u S g
  rw [ihomPoints_eq_uncurry]
  congr 1
  rw [Equiv.symm_apply_eq]
  exact (Work.ATOM.homFreeEquiv_naturality_target S u g).symm

end Work.ANALYTIC
