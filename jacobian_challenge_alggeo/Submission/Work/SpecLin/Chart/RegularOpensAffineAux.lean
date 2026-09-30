/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# First properties of the morphism `regularOpensMap C x ⟶ 𝔸¹_K`

This file collects the "cheap" properties of the morphism
`Work.SpecLin.Chart.regularOpensMap C x : (regularOpens C x).toScheme ⟶ Spec K[X]`:
that it is locally of finite type, quasi-compact and separated.
-/
import Mathlib
import Submission.Work.SpecLin.Chart.RegularOpensMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopCat TopCat.Presheaf Opposite
open scoped Classical

universe u

namespace Work.SpecLin.Chart

open Work.CurveBasics

variable {K : Type u} [Field K]

/-- `regularOpensMap C x` is locally of finite type. -/
theorem locallyOfFiniteType_regularOpensMap (C : Curve K) (x : C.functionField) :
    LocallyOfFiniteType (regularOpensMap C x) := by
  have h2 : LocallyOfFiniteType ((regularOpens C x).toScheme ↘ Spec (CommRingCat.of K)) :=
    show LocallyOfFiniteType ((regularOpens C x).ι ≫ C.hom) from inferInstance
  have h1 : LocallyOfFiniteType
      (regularOpensMap C x ≫ Spec.map (CommRingCat.ofHom Polynomial.C)) := by
    rw [regularOpensMap_over]; exact h2
  exact @locallyOfFiniteType_of_comp _ _ _ (regularOpensMap C x)
    (Spec.map (CommRingCat.ofHom Polynomial.C)) h1

/-- `regularOpensMap C x` is quasi-compact. -/
theorem quasiCompact_regularOpensMap (C : Curve K) (x : C.functionField) :
    QuasiCompact (regularOpensMap C x) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]
  haveI : TopologicalSpace.NoetherianSpace ↥(↑(regularOpens C x) : Set C.left) :=
    TopologicalSpace.NoetherianSpace.set (α := C.left) (↑(regularOpens C x) : Set C.left)
  exact TopologicalSpace.NoetherianSpace.compactSpace ↥(↑(regularOpens C x) : Set C.left)

/-- `regularOpensMap C x` is separated. -/
theorem isSeparated_regularOpensMap (C : Curve K) (x : C.functionField) :
    IsSeparated (regularOpensMap C x) := by
  have h2 : IsSeparated ((regularOpens C x).toScheme ↘ Spec (CommRingCat.of K)) :=
    show IsSeparated ((regularOpens C x).ι ≫ C.hom) from inferInstance
  have h1 : IsSeparated
      (regularOpensMap C x ≫ Spec.map (CommRingCat.ofHom Polynomial.C)) := by
    rw [regularOpensMap_over]; exact h2
  exact @IsSeparated.of_comp _ _ _ (regularOpensMap C x)
    (Spec.map (CommRingCat.ofHom Polynomial.C)) h1

/-- `regularOpensMap C x` is proper whenever it satisfies the valuative criterion. -/
theorem isProper_regularOpensMap_of_valuativeCriterion (C : Curve K) (x : C.functionField)
    (hvc : ValuativeCriterion.Existence (regularOpensMap C x)) :
    IsProper (regularOpensMap C x) where
  toIsSeparated := isSeparated_regularOpensMap C x
  toUniversallyClosed := by
    haveI := quasiCompact_regularOpensMap C x
    exact UniversallyClosed.of_valuativeCriterion _ hvc
  toLocallyOfFiniteType := locallyOfFiniteType_regularOpensMap C x

end Work.SpecLin.Chart
