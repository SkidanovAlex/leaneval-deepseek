import Mathlib
import Submission.Work.ANALYTIC.RealSideDefs
import Submission.Work.ANALYTIC.BoundedRealType
import Submission.Work.ANALYTIC.boundedReal_coprod
import Submission.Work.ANALYTIC.boundedReal_preservesFiniteProducts
import Submission.Work.ANALYTIC.boundedSeq_pullback_compat

/-!
# The sheaf condition for `∏^bnd ℝ` (assembled)

This file assembles the sheaf condition for the presheaf `boundedRealPresheaf`
(`Submission/Work/ANALYTIC/RealSideDefs.lean`) from the two halves

* `Work.ANALYTIC.boundedReal_preservesFiniteProducts` (module
  `Submission.Work.ANALYTIC.boundedReal_preservesFiniteProducts`), and
* the equalizer condition (the content below, which is the ℝ-analogue of
  `Work.ANALYTIC.boundedSeq_equalizerCondition`).

The abbreviation `boundedRealTypePresheaf` is imported from
`Submission.Work.ANALYTIC.BoundedRealType`.

## Why this file exists

The equalizer condition is also proved in `Submission/Work/ANALYTIC/boundedReal_equalizerCondition.lean`,
but that module *redefines* `boundedRealTypePresheaf` (rather than importing it from
`BoundedRealType`), so it cannot be imported together with `BoundedRealType` (which is needed for
`boundedReal_preservesFiniteProducts`).  The declarations below are therefore a copy of that
module's content in a form compatible with `BoundedRealType`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.regularTopology
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The comparison map of `boundedRealTypePresheaf` along `f : T ⟶ S` is precomposition with `f`:
`(f^* a)_n = a_n ∘ f`.  This is definitional. -/
lemma boundedReal_map_apply_eval {S T : LightProfinite} (f : T ⟶ S)
    (a : boundedRealSet S) (n : ℕ) (t : T) :
    (boundedRealTypePresheaf.map f.op a).1 n t = a.1 n (f t) := rfl

/-- Pullback along a surjection is injective: two bounded families of continuous `ℝ`-valued
functions on `B` that agree after precomposition with a surjection `π : X ⟶ B` already agree. -/
theorem boundedReal_map_injective {X B : LightProfinite} (π : X ⟶ B)
    (hπ : ∀ y : B, ∃ x : X, π x = y) (a b : boundedRealSet B)
    (h : boundedRealTypePresheaf.map π.op a = boundedRealTypePresheaf.map π.op b) : a = b := by
  apply Subtype.ext
  funext n
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  have h' : (boundedRealTypePresheaf.map π.op a : boundedRealSet X) =
      (boundedRealTypePresheaf.map π.op b : boundedRealSet X) := h
  have hx := congrArg (fun z : boundedRealSet X => (z.1 n) x) h'
  rw [boundedReal_map_apply_eval, boundedReal_map_apply_eval] at hx
  exact hx

/-- The compatibility of a family over `X` with the kernel pair of `π : X ⟶ B` says, pointwise,
that its coordinates are constant on the fibres of `π`.

Given `x y : X` with `π x = π y`, the two constant maps `z ↦ x` and `z ↦ y : X ⟶ X` have the same
composite with `π`, hence induce a map `w : X ⟶ pullback π π` with `w ≫ fst = const x` and
`w ≫ snd = const y`; evaluating the hypothesis at the point `w x` and using the definitional
description of the comparison maps as precomposition gives the claim. -/
theorem boundedReal_pullback_compat {X B : LightProfinite} (π : X ⟶ B) (a : boundedRealSet X)
    (ha : boundedRealTypePresheaf.map (CategoryTheory.Limits.pullback.fst π π).op a =
          boundedRealTypePresheaf.map (CategoryTheory.Limits.pullback.snd π π).op a) :
    ∀ (n : ℕ) (x y : X), π x = π y → a.1 n x = a.1 n y := by
  intro n x y hxy
  -- the two constant maps `z ↦ x` and `z ↦ y` agree after composition with `π`
  have hcompat : constHom X x ≫ π = constHom X y ≫ π := by
    ext z
    simpa using hxy
  -- hence they induce a map to the kernel pair
  let w : X ⟶ CategoryTheory.Limits.pullback π π :=
    Limits.pullback.lift (f := π) (g := π) (constHom X x) (constHom X y) hcompat
  -- whose projections evaluated at the point `x : X` are `x` and `y`
  have hfst : CategoryTheory.Limits.pullback.fst π π (w x) = x := by
    have h : w ≫ CategoryTheory.Limits.pullback.fst π π = constHom X x :=
      Limits.pullback.lift_fst (f := π) (g := π) (constHom X x) (constHom X y) hcompat
    simpa only [ConcreteCategory.comp_apply, constHom_apply] using
      congrArg (fun (m : X ⟶ X) => (m : X → X) x) h
  have hsnd : CategoryTheory.Limits.pullback.snd π π (w x) = y := by
    have h : w ≫ CategoryTheory.Limits.pullback.snd π π = constHom X y :=
      Limits.pullback.lift_snd (f := π) (g := π) (constHom X x) (constHom X y) hcompat
    simpa only [ConcreteCategory.comp_apply, constHom_apply] using
      congrArg (fun (m : X ⟶ X) => (m : X → X) x) h
  -- evaluating the hypothesis at that point gives the claim
  have hcoord := congrArg (fun b : boundedRealSet (CategoryTheory.Limits.pullback π π) =>
    (b.1 n) (w x)) ha
  rw [boundedReal_map_apply_eval (CategoryTheory.Limits.pullback.fst π π) a n (w x),
    boundedReal_map_apply_eval (CategoryTheory.Limits.pullback.snd π π) a n (w x)]
    at hcoord
  rw [hfst, hsnd] at hcoord
  exact hcoord

/-- Descent of a bounded family of continuous `ℝ`-valued functions along a surjection `π : X ⟶ B`
whose coordinates are constant on the fibres of `π`.

The descended coordinates `y ↦ a_n (c y)` are continuous because `π` is a quotient map (compact
source, Hausdorff target) and they are uniformly bounded by *the same* bound `N`, because every
point of `B` is the image of a point of `X`. -/
theorem boundedReal_descend {X B : LightProfinite} (π : X ⟶ B)
    (hπ : ∀ y : B, ∃ x : X, π x = y) (a : boundedRealSet X)
    (ha : ∀ (n : ℕ) (x y : X), π x = π y → a.1 n x = a.1 n y) :
    ∃ b : boundedRealSet B, ∀ (n : ℕ) (x : X), b.1 n (π x) = a.1 n x := by
  classical
  have hsurj : Function.Surjective (π : X → B) := fun y => hπ y
  have hquot : Topology.IsQuotientMap (π : X → B) :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj π.hom.hom.continuous
  -- a choice of preimage for every point of `B`
  let c : B → X := fun y => Classical.choose (hπ y)
  have hc : ∀ y : B, π (c y) = y := fun y => Classical.choose_spec (hπ y)
  -- the descended candidate is constant on the fibres of `π`
  have hcomp : ∀ n : ℕ,
      (fun y : B => a.1 n (c y)) ∘ (π : X → B) = fun x : X => a.1 n x := by
    intro n
    funext x
    exact ha n (c (π x)) x (hc (π x))
  -- hence it is continuous, because `π` is a quotient map
  have hcont : ∀ n : ℕ, Continuous (fun y : B => a.1 n (c y)) := by
    intro n
    refine (Topology.IsQuotientMap.continuous_iff hquot).mpr ?_
    rw [hcomp n]
    exact (a.1 n).continuous
  obtain ⟨N, hN⟩ := a.2
  refine ⟨⟨fun n => ⟨fun y => a.1 n (c y), hcont n⟩, ⟨N, fun n y => hN n (c y)⟩⟩, ?_⟩
  intro n x
  exact congrFun (hcomp n) x

/-- **The equalizer condition for `∏^bnd ℝ`**: the presheaf of uniformly bounded families of
continuous real-valued functions on a light profinite set takes the kernel pair of every effective
epimorphism (i.e. of every continuous surjection) to an equalizer diagram. -/
theorem boundedRealSheafEqualizer :
    CategoryTheory.regularTopology.EqualizerCondition (CategoryTheory.Functor.comp Work.ANALYTIC.boundedRealPresheaf (CategoryTheory.forget (ModuleCat ℤ))) := by
  refine EqualizerCondition.mk boundedRealTypePresheaf (fun X B π _ _ => ?_)
  constructor
  · -- injectivity of the comparison map
    intro a b h
    refine boundedReal_map_injective π (fun y => ?_) a b (congrArg Subtype.val h)
    exact (LightProfinite.effectiveEpi_iff_surjective π).mp inferInstance y
  · -- the lifting property: a compatible family over `X` descends to `B`
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := boundedReal_descend π
      (fun y => (LightProfinite.effectiveEpi_iff_surjective π).mp inferInstance y) a
      (boundedReal_pullback_compat π a ha)
    refine ⟨b, ?_⟩
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    funext n
    exact ContinuousMap.ext (fun x => hb n x)

end Work.ANALYTIC
