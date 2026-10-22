import Mathlib
import Submission.Work.REFL.Basic

/-!
# AREA REFL — solidity is locality for the test family `W`

This file proves `Work.REFL.IsSolidIsLocalStatement` (RC Prop. 3.2.5) from the points
description `Work.REFL.PrePointsStatement` of the endomorphism `pre oneMinusShift`:

> `M` is solid (`IsIso ((pre oneMinusShift).app M)`) if and only if `M` is local for the small
> family `solidW` of test maps `testMap S = (1 - S) ⊗ id_{ℤ[S]}`.

The argument has three steps, each isolated below.

* `isIso_preShift_iff_app_bijective` — a morphism of light condensed abelian groups is an
  isomorphism iff all its components at light profinite sets are bijective
  (`ObjectProperty.isIso_hom_iff` + `NatTrans.isIso_iff_isIso_app` +
  `ConcreteCategory.isIso_iff_bijective`).
* `app_bijective_iff_precomp_testMap` — under the points equivalence
  `ihomPPoints M S : (ihom P M)(S) ≃ (P ⊗ ℤ[S] ⟶ M)` the component of `preShift M` at `S` becomes
  precomposition with `testMap S`; this is exactly the content of `PrePointsStatement`.
* `precomp_testMap_bijective_of_iso` — this bijectivity condition is invariant under
  isomorphisms `S ≅ T` of light profinite sets, by naturality of the whiskering
  `oneMinusShift ▷ -` (`whisker_exchange`). Hence it suffices to test it on a small skeleton
  (`testSpace`), which is what `solidW` does.

## Contents

* `Work.REFL.precompTestMap`
* `Work.REFL.isIso_preShift_iff_app_bijective`
* `Work.REFL.app_bijective_iff_precomp_testMap`
* `Work.REFL.precomp_testMap_bijective_of_iso`
* `Work.REFL.isSolid_iff_solidW`
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- Precomposition with the test map `testMap S` on maps out of `P ⊗ ℤ[S]`. -/
abbrev precompTestMap (M : LightCondAb) (S : LightProfinite.{0}) :
    (P ⊗ (free ℤ).obj S.toCondensed ⟶ M) → (P ⊗ (free ℤ).obj S.toCondensed ⟶ M) :=
  fun g => testMap S ≫ g

/-- A morphism of light condensed abelian groups is an isomorphism iff all of its components are
bijective. -/
lemma isIso_preShift_iff_app_bijective (M : LightCondAb) :
    IsIso (preShift M) ↔ ∀ X : (LightProfinite.{0})ᵒᵖ,
      Function.Bijective ((preShift M).hom.app X) := by
  refine ((ObjectProperty.isIso_hom_iff (preShift M)).symm).trans ?_
  refine (NatTrans.isIso_iff_isIso_app ((preShift M).hom)).trans ?_
  exact forall_congr' fun X => ConcreteCategory.isIso_iff_bijective _

/-- The component of `preShift M` at the sections over `S` is, under the points equivalence
`ihomPPoints M S`, precomposition with `testMap S`. -/
lemma app_bijective_iff_precomp_testMap (h : PrePointsStatement) (M : LightCondAb)
    (S : LightProfinite.{0}) :
    Function.Bijective ((preShift M).hom.app (Opposite.op S)) ↔
      Function.Bijective (precompTestMap M S) := by
  have hcomp : ⇑((preShift M).hom.app (Opposite.op S)) =
      ⇑(ihomPPoints M S).symm ∘ precompTestMap M S ∘ ⇑(ihomPPoints M S) := by
    funext x
    exact h M S x
  rw [hcomp]
  exact (Function.Bijective.of_comp_iff'
      (Equiv.bijective (ihomPPoints M S).symm)
      (fun x => testMap S ≫ (ihomPPoints M S) x)).trans
    (Function.Bijective.of_comp_iff _ (Equiv.bijective (ihomPPoints M S)))

/-- The bijectivity of precomposition with `testMap` is transported along isomorphisms of light
profinite sets, by naturality of `oneMinusShift ▷ -`. -/
lemma precomp_testMap_bijective_of_iso (M : LightCondAb) {S T : LightProfinite.{0}}
    (φ : S ≅ T) :
    Function.Bijective (precompTestMap M S) ↔ Function.Bijective (precompTestMap M T) := by
  let θ : P ⊗ (free ℤ).obj S.toCondensed ⟶ P ⊗ (free ℤ).obj T.toCondensed :=
    P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ.hom
  let Ψ : (P ⊗ (free ℤ).obj T.toCondensed ⟶ M) → (P ⊗ (free ℤ).obj S.toCondensed ⟶ M) :=
    fun g => θ ≫ g
  have hΨ : Function.Bijective Ψ := by
    have : Ψ = ⇑(Iso.homFromEquiv (asIso θ)).symm := rfl
    rw [this]
    exact Equiv.bijective _
  have hcomp : precompTestMap M S ∘ Ψ = Ψ ∘ precompTestMap M T := by
    funext g
    dsimp only [Function.comp_apply]
    simp only [Ψ, θ, precompTestMap, testMap]
    rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  rw [← Function.Bijective.of_comp_iff _ hΨ, hcomp, Function.Bijective.of_comp_iff' hΨ]

/-- **Area REFL, hole 2.** `M` is solid iff it is local for the small family `solidW` of test
morphisms (RC Prop. 3.2.5). -/
theorem isSolid_iff_solidW (h : Work.REFL.PrePointsStatement) : Work.REFL.IsSolidIsLocalStatement := by
  intro M
  refine ((show isSolid M ↔ IsIso (preShift M) from Iff.rfl)).trans ?_
  refine (isIso_preShift_iff_app_bijective M).trans ?_
  rw [solidW_isLocal_iff M]
  constructor
  · intro hS i
    rw [← app_bijective_iff_precomp_testMap h M (testSpace i)]
    exact hS (Opposite.op (testSpace i))
  · intro hi X
    obtain ⟨S, rfl⟩ := Opposite.op_surjective X
    rw [app_bijective_iff_precomp_testMap h M S]
    exact (precomp_testMap_bijective_of_iso M
      ((equivSmallModel LightProfinite.{0}).unitIso.app S)).mpr
      (hi ((equivSmallModel LightProfinite.{0}).functor.obj S))

end Work.REFL
