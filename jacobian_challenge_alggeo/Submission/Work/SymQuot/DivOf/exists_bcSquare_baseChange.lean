/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change squares iterate

Let `C` be a curve over a field `K` and let `K → F → F'` be a tower of field extensions.
The base changes `C_F = C ×_K Spec F` and `C_{F'} = C ×_K Spec F'` are related by the
cartesian square

```
C_{F'}  ⟶  C_F
  ↓         ↓
Spec F' ⟶ Spec F
```

obtained by pasting the two cartesian squares defining `C_{F'}` and `C_F` over `Spec K`
(this is the content of `towerHom` and `isPullback_tower` below; the map `C_{F'} ⟶ C_F` is
the one induced by the universal property of the pullback `C_F`, and the square is cartesian
because the outer square `C_{F'} ⟶ C_F ⟶ C` over `Spec F' ⟶ Spec F ⟶ Spec K` is the defining
cartesian square of `C_{F'}` and the square `C_F ⟶ C` over `Spec F ⟶ Spec K` is cartesian).

Consequently there is a base-change square `BCSquare (C.baseChange F) (C.baseChange F')`,
which is the statement proved here.

## Main results

* `Work.SymQuot.DivOf.BCSquareBaseChange.specMap_tower` — `Spec F' ⟶ Spec K` factors through
  `Spec F`;
* `Work.SymQuot.DivOf.BCSquareBaseChange.towerHom` — the canonical morphism `C_{F'} ⟶ C_F`;
* `Work.SymQuot.DivOf.BCSquareBaseChange.isPullback_tower` — the tower square is cartesian;
* `Work.SymQuot.DivOf.exists_bcSquare_baseChange` — base-change squares iterate.
-/
import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.SpecLin.Alt.Pasting

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

namespace BCSquareBaseChange

open Work.CurveBasics

variable {K : Type u} [Field K] {C : Curve K}
variable {F : Type u} [Field F] [Algebra K F]
variable {F' : Type u} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

/-- Along a tower of field extensions `K → F → F'`, the structure morphism
`Spec F' ⟶ Spec K` factors as `Spec F' ⟶ Spec F ⟶ Spec K`. -/
lemma specMap_tower : Curve.specMap K F' = Curve.specMap F F' ≫ Curve.specMap K F := by
  rw [Curve.specMap, Curve.specMap, Curve.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact IsScalarTower.algebraMap_apply K F F' x

/-- **The canonical morphism of base changes along a tower of field extensions.**
The universal property of the pullback `C_F = C ×_K Spec F` produces a morphism
`C_{F'} ⟶ C_F` from the projection `C_{F'} ⟶ C` and the composite `C_{F'} ⟶ Spec F' ⟶ Spec F`. -/
noncomputable def towerHom : Curve.baseChangeLeft C F' ⟶ Curve.baseChangeLeft C F :=
  pullback.lift (Curve.baseChangeFst C F') (Curve.baseChangeHom C F' ≫ Curve.specMap F F')
    (by
      rw [Category.assoc, ← specMap_tower]
      exact pullback.condition)

/-- The morphism `C_{F'} ⟶ C_F` is compatible with the projections to `C`. -/
lemma towerHom_fst : towerHom (C := C) ≫ Curve.baseChangeFst C F = Curve.baseChangeFst C F' :=
  pullback.lift_fst _ _ _

/-- The morphism `C_{F'} ⟶ C_F` is compatible with the structure morphisms to `Spec F`. -/
lemma towerHom_snd :
    towerHom (C := C) ≫ Curve.baseChangeHom C F
      = Curve.baseChangeHom C F' ≫ Curve.specMap F F' :=
  pullback.lift_snd _ _ _

/-- **The tower square is cartesian.**  Pasting the cartesian square defining `C_{F'}` with the
cartesian square defining `C_F` shows that the square with corners `C_{F'}`, `C_F`, `Spec F'`,
`Spec F` is a pullback. -/
theorem isPullback_tower :
    IsPullback (towerHom (C := C)) (Curve.baseChangeHom C F') (Curve.baseChangeHom C F)
      (Curve.specMap F F') := by
  refine IsPullback.of_right (h₁₂ := Curve.baseChangeFst C F) (h₂₂ := Curve.specMap K F)
    (v₁₃ := C.hom) ?_ ?_ ?_
  · rw [towerHom_fst, ← specMap_tower]
    exact IsPullback.of_hasPullback C.hom (Curve.specMap K F')
  · exact towerHom_snd
  · exact IsPullback.of_hasPullback C.hom (Curve.specMap K F)

end BCSquareBaseChange

/-- **Base-change squares iterate.**  For a tower of field extensions `K → F → F'` and a curve
`C` over `K`, the base changes `C_F` and `C_{F'}` fit into a base-change square, so in particular
`Work.CurveBasics.Curve.BCSquare (C.baseChange F) (C.baseChange F')` is nonempty. -/
theorem exists_bcSquare_baseChange {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {F' : Type u} [Field F'] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] :
    Nonempty (Work.CurveBasics.Curve.BCSquare (C.baseChange F) (C.baseChange F')) :=
  ⟨⟨BCSquareBaseChange.towerHom (C := C), BCSquareBaseChange.isPullback_tower (C := C)⟩⟩

end Work.SymQuot.DivOf
