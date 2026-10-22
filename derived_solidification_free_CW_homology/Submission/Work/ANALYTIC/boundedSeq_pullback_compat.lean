import Mathlib
import Submission.Work.ANALYTIC.BoundedType

/-!
# The compatibility of `∏^bnd ℤ` with the kernel pair of a map

`boundedSeqSet S` is the set of uniformly bounded families of continuous `ℤ`-valued functions on a
light profinite set `S` (`Submission/Work/ANALYTIC/Bounded.lean`), and `boundedTypePresheaf` is the
underlying presheaf of types of `boundedPresheaf`.

The equalizer condition of `boundedTypePresheaf` for a map `π : X ⟶ B` says that
`boundedTypePresheaf` sends the two projections of the kernel pair `pullback π π` to maps with the
same image on every element `a` of `boundedSeqSet X`.  This module proves that this condition is
exactly the statement that the coordinates of `a` are constant on the fibres of `π`, which is what
the descent argument (`Submission/Work/ANALYTIC/boundedSeq_descend.lean`) consumes.

The proof is pointwise: given `x y : X` with `π x = π y`, the two constant maps
`z ↦ x, z ↦ y : X ⟶ X` have the same composite with `π`, hence induce a map
`w : X ⟶ pullback π π` with `w ≫ fst = const x` and `w ≫ snd = const y`; applying the hypothesis
`a` at the point `w x` (the image of the point `x : X` under `w`) and using the definitional
description of the comparison maps as precomposition gives the claim.
-/

open CategoryTheory Limits LightProfinite

noncomputable section

namespace Work.ANALYTIC

/-- The comparison map of `boundedTypePresheaf` along `f : T ⟶ S` is precomposition with `f`:
`(f^* a)_n = a_n ∘ f`.  This is definitional. -/
lemma boundedTypePresheaf_map_apply_eval {S T : LightProfinite} (f : T ⟶ S)
    (a : boundedSeqSet S) (n : ℕ) (t : T) :
    (boundedTypePresheaf.map f.op a).1 n t = a.1 n (f t) := rfl

/-- The constant map `z ↦ x` as a morphism `X ⟶ X` of light profinite sets.  It is used to
produce points of the kernel pair `pullback π π` from two points of `X` lying in the same fibre
of `π`. -/
def constHom (X : LightProfinite) (x : X) : X ⟶ X :=
  ConcreteCategory.ofHom ⟨fun _ => x, continuous_const⟩

@[simp]
lemma constHom_apply (X : LightProfinite) (x z : X) : constHom X x z = x := rfl

/-- The two projections of the kernel pair of `π` have the same action on an element of
`boundedSeqSet X` only if its coordinates are constant on the fibres of `π`. -/
theorem boundedSeq_pullback_compat {X B : LightProfinite} (π : X ⟶ B) (a : boundedSeqSet X)
    (ha : boundedTypePresheaf.map (CategoryTheory.Limits.pullback.fst π π).op a =
          boundedTypePresheaf.map (CategoryTheory.Limits.pullback.snd π π).op a) :
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
  have hcoord := congrArg (fun b : boundedSeqSet (CategoryTheory.Limits.pullback π π) =>
    (b.1 n) (w x)) ha
  rw [boundedTypePresheaf_map_apply_eval (CategoryTheory.Limits.pullback.fst π π) a n (w x),
    boundedTypePresheaf_map_apply_eval (CategoryTheory.Limits.pullback.snd π π) a n (w x)]
    at hcoord
  rw [hfst, hsnd] at hcoord
  exact hcoord

end Work.ANALYTIC
