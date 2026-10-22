import Submission.Work.REFL.isSolid_iff_solidW
import Submission.Work.REFL.pre_app_points

/-!
# AREA REFL — RC Prop. 3.2.5 in usable form

`Work.REFL.isSolid_iff_solidW` proves that solidity is locality for the *small skeleton*
`solidW` of test morphisms `testMap S = (1 − S) ⊗ id_{ℤ[S]}` (this is the form the reflection
construction needs, because the family has to be small; it is stated relative to the points
description `Work.REFL.pre_app_points`).

For applications one usually wants the criterion for *every* light profinite set `S`, and without
passing the points description around.  This file records that form, together with the two
one-sided consequences and an `Equiv` packaging of the bijection.  Nothing new is proved about
the mathematics: everything is assembled from the three ingredients already established in
`isSolid_iff_solidW.lean`, namely

* `Work.REFL.isIso_preShift_iff_app_bijective` — a map of light condensed abelian groups is an
  isomorphism iff all its section maps are bijective;
* `Work.REFL.app_bijective_iff_precomp_testMap` — the section map of `pre oneMinusShift` is
  precomposition with `testMap S` (this is `Work.REFL.pre_app_points`);
* the isomorphism-invariance of the condition, `Work.REFL.precomp_testMap_bijective_of_iso`.

Contents:

* `Work.REFL.solidW_isLocal_eq_isSolid` — the object property `solidW.isLocal` equals `isSolid`
  (this is the `hloc` identity fed to `MorphismProperty.isRightAdjoint_ι_isLocal` in `Main.lean`);
* `Work.REFL.isSolid_iff_bijective_testMap` — RC Prop. 3.2.5 over all `S : LightProfinite`;
* `Work.REFL.bijective_testMap_of_isSolid` / `Work.REFL.isSolid_of_bijective_testMap` — the two
  directions separately;
* `Work.REFL.precompTestMapEquiv` — the bijection as an equivalence of `Hom`-types, with its
  inverse available as `(precompTestMapEquiv M hM S).symm`.

The last two are the exact form of the "null-sequence" input used downstream (RC Lemma 3.3.2):
for a solid target `M`, precomposition with `(1 − S) ⊗ id_{ℤ[S]}` is invertible on
`Hom(P ⊗ ℤ[S], M)`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The locality property of the small test family `solidW` *is* the property of being solid;
hence `Solid` is exactly the class of objects local for `solidW`. -/
theorem solidW_isLocal_eq_isSolid : solidW.isLocal = isSolid :=
  funext fun M => propext (_root_.Work.REFL.isSolid_iff_solidW pre_app_points M).symm

/-- **RC Prop. 3.2.5 over all light profinite sets.** `M` is solid iff for every light profinite
`S` the precomposition map
`Hom(P ⊗ ℤ[S], M) → Hom(P ⊗ ℤ[S], M)`, `g ↦ testMap S ≫ g` with `testMap S = (1 − S) ⊗ id`,
is a bijection. -/
theorem isSolid_iff_bijective_testMap (M : LightCondAb) :
    isSolid M ↔ ∀ S : LightProfinite.{0}, Function.Bijective (precompTestMap M S) := by
  refine ((show isSolid M ↔ IsIso (preShift M) from Iff.rfl)).trans ?_
  refine (isIso_preShift_iff_app_bijective M).trans ?_
  constructor
  · intro hS S
    rw [← app_bijective_iff_precomp_testMap pre_app_points M S]
    exact hS (Opposite.op S)
  · intro hS X
    obtain ⟨S, rfl⟩ := Opposite.op_surjective X
    rw [app_bijective_iff_precomp_testMap pre_app_points M S]
    exact hS S

/-- For a solid target, precomposition with the test map `(1 − S) ⊗ id_{ℤ[S]}` is bijective on
`Hom(P ⊗ ℤ[S], M)`. -/
theorem bijective_testMap_of_isSolid (M : LightCondAb) (hM : isSolid M) (S : LightProfinite.{0}) :
    Function.Bijective (precompTestMap M S) :=
  (isSolid_iff_bijective_testMap M).mp hM S

/-- Conversely, bijectivity of all the test maps implies solidity. -/
theorem isSolid_of_bijective_testMap (M : LightCondAb)
    (h : ∀ S : LightProfinite.{0}, Function.Bijective (precompTestMap M S)) : isSolid M :=
  (isSolid_iff_bijective_testMap M).mpr h

/-- For a solid target, precomposition with the test map is an equivalence of `Hom`-types; its
inverse is the "solve `(1 − S) ⊗ id ≫ f = g`" operation used in the null-sequence argument. -/
def precompTestMapEquiv (M : LightCondAb) (hM : isSolid M) (S : LightProfinite.{0}) :
    (P ⊗ (free ℤ).obj S.toCondensed ⟶ M) ≃ (P ⊗ (free ℤ).obj S.toCondensed ⟶ M) :=
  Equiv.ofBijective _ (bijective_testMap_of_isSolid M hM S)

@[simp]
theorem precompTestMapEquiv_apply (M : LightCondAb) (hM : isSolid M) (S : LightProfinite.{0})
    (g : P ⊗ (free ℤ).obj S.toCondensed ⟶ M) :
    precompTestMapEquiv M hM S g = precompTestMap M S g := rfl

@[simp]
theorem precompTestMap_precompTestMapEquiv_symm (M : LightCondAb) (hM : isSolid M)
    (S : LightProfinite.{0}) (g : P ⊗ (free ℤ).obj S.toCondensed ⟶ M) :
    precompTestMap M S ((precompTestMapEquiv M hM S).symm g) = g :=
  (precompTestMapEquiv M hM S).apply_symm_apply g

@[simp]
theorem precompTestMapEquiv_symm_precompTestMap (M : LightCondAb) (hM : isSolid M)
    (S : LightProfinite.{0}) (g : P ⊗ (free ℤ).obj S.toCondensed ⟶ M) :
    (precompTestMapEquiv M hM S).symm (precompTestMap M S g) = g :=
  (precompTestMapEquiv M hM S).symm_apply_apply g

end Work.REFL
