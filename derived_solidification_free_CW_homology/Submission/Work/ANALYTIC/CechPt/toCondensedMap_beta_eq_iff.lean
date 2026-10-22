import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs

/-!
# The binary expansion as a map of light condensed sets: equality of composites

For a light profinite set `S` and `u v : S ⟶ C` (where `C = {0,1}^ℕ` is the Cantor set), the
composites of `u`, `v` with the binary expansion `beta : C ⟶ [0,1]` agree as morphisms of light
condensed sets if and only if `binExp (u s) = binExp (v s)` for all `s : ↥S`.

The two auxiliary lemmas below describe the composite `lightProfiniteToLightCondSet.map u ≫ beta`
at a test object: its value at `x : T ⟶ S` is the continuous map `z ↦ binExp (u (x z))`.  This is
definitional (`rfl`), the only work being to state it in the shape in which it appears in a goal.
-/

open CategoryTheory Limits LightProfinite LightCondensed

namespace Work.ANALYTIC.CechPt

open _root_.LightCondensed

/-- The composite `lightProfiniteToLightCondSet.map u ≫ beta` evaluated at a point
`x : T ⟶ S` of the representable sheaf of `S` is the continuous map `z ↦ binExp (u (x z))`. -/
lemma compMapBeta_apply {S T : LightProfinite.{0}} (u : S ⟶ cantor) (x : T ⟶ S) :
    ((lightProfiniteToLightCondSet.map u ≫ beta).hom.app (Opposite.op T)) x =
      (⟨fun z => binExp (u (x z)),
        binExp_continuous.comp ((ConcreteCategory.hom u).continuous.comp
          (ConcreteCategory.hom x).continuous)⟩ : C(↥T, ↥unitInterval)) := rfl

/-- The same statement with the test object `T` written as an object of `LightProfiniteᵒᵖ`, in the
shape in which the application of `x` appears after extensionality. -/
lemma compMapBeta_toFun {S : LightProfinite.{0}} (u : S ⟶ cantor) {T : (LightProfinite.{0})ᵒᵖ}
    (x : T.unop ⟶ S) :
    (ConcreteCategory.hom ((lightProfiniteToLightCondSet.map u ≫ beta).hom.app T)).toFun x =
      (⟨fun z => binExp (u (x z)),
        binExp_continuous.comp ((ConcreteCategory.hom u).continuous.comp
          (ConcreteCategory.hom x).continuous)⟩ : C(↥T.unop, ↥unitInterval)) := rfl

theorem toCondensedMap_beta_eq_iff {S : LightProfinite.{0}}
    (u v : S ⟶ Work.ANALYTIC.CechPt.cantor) :
    CategoryTheory.CategoryStruct.comp (lightProfiniteToLightCondSet.map u)
        Work.ANALYTIC.CechPt.beta =
      CategoryTheory.CategoryStruct.comp (lightProfiniteToLightCondSet.map v)
        Work.ANALYTIC.CechPt.beta ↔
      ∀ s : ↥S, Work.ANALYTIC.CechPt.binExp (u s) = Work.ANALYTIC.CechPt.binExp (v s) := by
  constructor
  · -- evaluate the equality of morphisms at `S` and at the generic point `𝟙 S`
    intro h s
    have h1 :
        (ConcreteCategory.hom ((lightProfiniteToLightCondSet.map u ≫ beta).hom.app
          (Opposite.op S))).toFun (𝟙 S) =
        (ConcreteCategory.hom ((lightProfiniteToLightCondSet.map v ≫ beta).hom.app
          (Opposite.op S))).toFun (𝟙 S) :=
      congrArg (fun f : LightProfinite.toCondensed S ⟶ intervalCond =>
        (ConcreteCategory.hom (f.hom.app (Opposite.op S))).toFun (𝟙 S)) h
    have h3 : (⟨fun z => binExp (u ((𝟙 S) z)),
          binExp_continuous.comp ((ConcreteCategory.hom u).continuous.comp
            (ConcreteCategory.hom (𝟙 S)).continuous)⟩ : C(↥S, ↥unitInterval)) =
        (⟨fun z => binExp (v ((𝟙 S) z)),
          binExp_continuous.comp ((ConcreteCategory.hom v).continuous.comp
            (ConcreteCategory.hom (𝟙 S)).continuous)⟩ : C(↥S, ↥unitInterval)) := by
      rw [← compMapBeta_toFun u (𝟙 S), ← compMapBeta_toFun v (𝟙 S)]
      exact h1
    have h4 := congrArg (fun g : C(↥S, ↥unitInterval) => g s) h3
    simpa using h4
  · -- two morphisms out of a representable are equal as soon as they agree at every point
    intro h
    apply LightCondensed.hom_ext
    intro T
    ext x
    rw [compMapBeta_toFun u x, compMapBeta_toFun v x]
    apply ContinuousMap.ext
    intro z
    show binExp (u ((ConcreteCategory.hom x) z)) = binExp (v ((ConcreteCategory.hom x) z))
    exact h ((ConcreteCategory.hom x) z)

end Work.ANALYTIC.CechPt
