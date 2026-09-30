/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv, B3: the `K`-point of `C` underlying an `F`-point of `C_L`

For `K → L → F` and a curve `C` over `K`, an `F`-point `x : Spec_L F ⟶ C_L` (in `Sch L`)
composes with the projection `(C_L) ⟶ C` to a point `bcPtK x` of `C` over `F` (in `Sch K`).
This is the point-level shadow of `Work.BcDiv.bcDiv`: the comparison square `bcSq` sends the
closed point of `bcPtK x` to the closed point of `x`, so `bcDiv (ptDiv x) = ptDiv (bcPtK x)`
(`Work.BcDiv.bcDiv_ptDiv`), with ramification index `1` (`Work.BcDiv.ramIdx_cmp`).

## Main definitions

* `Work.BcDiv.bcPtK` — the `K`-structure on the composite point.

## Main results

* `Work.BcDiv.bcPtK_left` — its underlying morphism of schemes.
-/
import Submission.Work.BcDiv.Basic
import Submission.Work.SpecLin.Points.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.BcDiv

noncomputable section

variable {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L] [Algebra K L]
  {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- **The `K`-point of `C` underlying an `F`-point of `C_L`**: an `F`-point `x` of the base
change `C_L` (a morphism `Spec_L F ⟶ C_L` in `Sch L`) gives, by composition with the projection
`(C_L) ⟶ C`, an `F`-point of `C` over `K`. -/
def bcPtK (x : Work.SpecLin.CurveFPt (C.baseChange L) F) : Work.SpecLin.CurveFPt C F :=
  Over.homMk (x.left ≫ (Curve.bcSquare C L).π) (by
    have hπ : (Curve.bcSquare C L).π = pullback.fst C.hom (Curve.specMap K L) := rfl
    have hw : x.left ≫ pullback.snd C.hom (Curve.specMap K L)
        = (Work.SpecLin.specOf (K := L) F).hom := Over.w x
    rw [Category.assoc, hπ, pullback.condition, ← Category.assoc, hw]
    show Spec.map (CommRingCat.ofHom (algebraMap L F))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))
      = Spec.map (CommRingCat.ofHom (algebraMap K F))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L F])

@[simp]
theorem bcPtK_left (x : Work.SpecLin.CurveFPt (C.baseChange L) F) :
    (bcPtK x).left = x.left ≫ (Curve.bcSquare C L).π := rfl

/-- `bcPtK` is natural in the field: the point attached to the base change of `x` is the base
change of the point attached to `x`, where the `K`-algebra structure on `F'` is the restriction
of scalars of the `L`-algebra structure. -/
theorem bcPtK_map {F' : Type u} [Field F'] [Algebra L F'] [Algebra K F']
    [IsScalarTower K L F'] (e : F →ₐ[L] F') (x : Work.SpecLin.CurveFPt (C.baseChange L) F) :
    bcPtK (Work.SpecLin.RPt.map e x)
      = Work.SpecLin.RPt.map (e.restrictScalars K) (bcPtK x) := by
  apply Over.OverMorphism.ext
  simp only [bcPtK_left, Over.comp_left, Work.SpecLin.RPt.map, Work.SpecLin.specOfMap]
  rfl

end

end Work.BcDiv
