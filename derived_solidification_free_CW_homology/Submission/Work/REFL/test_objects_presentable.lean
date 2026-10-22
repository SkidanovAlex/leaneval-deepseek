import Mathlib
import Submission.Work.REFL.Basic

/-!
# AREA REFL — the test objects `P ⊗ ℤ[S]` are finitely presentable

This module proves `Work.REFL.TestObjectsPresentable` from `Work.REFL.AtomsPresentable`
(the free objects `ℤ[S]` on light profinite sets are `ℵ₀`-presentable).

The argument is the one sketched in `Submission/Blueprint/Interfaces.lean`:

* `P` is a retract of `ℤ[ℕ∪{∞}]` (`LightCondensed.P_retract`), so tensoring with `ℤ[S]`
  exhibits `P ⊗ ℤ[S]` as a retract of `ℤ[ℕ∪{∞}] ⊗ ℤ[S]` (`retract_P_tensor`);
* the free light condensed abelian group functor is strong monoidal
  (`LightCondensed.free ℤ`), and so is `lightProfiniteToLightCondSet`, whence
  `ℤ[A] ⊗ ℤ[B] ≅ ℤ[A ⊗ B]` for light profinite `A`, `B` (`free_tensor_free`);
* `IsCardinalPresentable` is stable under isomorphisms and under retracts
  (`isCardinalPresentable_of_iso`, `Retract.isCardinalPresentable`);
* so `AtomsPresentable` at the light profinite set `(ℕ∪{∞}) ⊗ S` gives the result.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **The free light condensed abelian group is strong monoidal**, so that
`ℤ[S] ⊗ ℤ[T] ≅ ℤ[S ⊗ T]` for light profinite `S`, `T`.

The left isomorphism is the structure morphism `μ` of the monoidal functor
`(free ℤ) : LightCondSet ⥤ LightCondAb` (an isomorphism because a monoidal functor in the
sense of Mathlib is strong monoidal); the right one is the same for the monoidal functor
`lightProfiniteToLightCondSet : LightProfinite ⥤ LightCondSet`, applied through `free ℤ`. -/
def free_tensor_free (S T : LightProfinite.{0}) :
    (free ℤ).obj S.toCondensed ⊗ (free ℤ).obj T.toCondensed ≅
      (free ℤ).obj (S ⊗ T).toCondensed :=
  Functor.Monoidal.μIso (free ℤ) _ _ ≪≫
    (free ℤ).mapIso (Functor.Monoidal.μIso lightProfiniteToLightCondSet S T)

/-- **`P ⊗ X` is a retract of `ℤ[ℕ∪{∞}] ⊗ X`**, obtained by tensoring the retraction
`LightCondensed.P_retract` (the split surjection `ℤ[ℕ∪{∞}] ↠ P`) with `X`. -/
def retract_P_tensor (X : LightCondAb) :
    Retract (P ⊗ X) ((free ℤ).obj (ℕ∪{∞}).toCondensed ⊗ X) :=
  Retract.map LightCondensed.P_retract (tensorRight X)

/-- The test objects `P ⊗ ℤ[S]` are `ℵ₀`-presentable (finitely presentable), because they are
retracts of the free objects `ℤ[(ℕ∪{∞}) ⊗ S]`, which are `ℵ₀`-presentable by
`Work.REFL.AtomsPresentable`. -/
theorem test_objects_presentable (h : Work.REFL.AtomsPresentable) : Work.REFL.TestObjectsPresentable := by
  intro S
  have e := free_tensor_free (ℕ∪{∞} : LightProfinite.{0}) S
  have h1 : IsCardinalPresentable
      ((free ℤ).obj (((ℕ∪{∞} : LightProfinite.{0}) ⊗ S).toCondensed))
      (Cardinal.aleph0 : Cardinal.{0}) := h ((ℕ∪{∞} : LightProfinite.{0}) ⊗ S)
  have h2 : IsCardinalPresentable
      ((free ℤ).obj ((ℕ∪{∞} : LightProfinite.{0}).toCondensed) ⊗ (free ℤ).obj S.toCondensed)
      (Cardinal.aleph0 : Cardinal.{0}) :=
    isCardinalPresentable_of_iso e.symm (Cardinal.aleph0 : Cardinal.{0})
  have hr : Retract (P ⊗ (free ℤ).obj S.toCondensed)
      ((free ℤ).obj ((ℕ∪{∞} : LightProfinite.{0}).toCondensed) ⊗ (free ℤ).obj S.toCondensed) :=
    retract_P_tensor ((free ℤ).obj S.toCondensed)
  exact Retract.isCardinalPresentable hr (Cardinal.aleph0 : Cardinal.{0})

end Work.REFL
