/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The base-change comparison on field points (area SY)

This file records the point-level coherence of the base-change comparison
`symβ : Symⁿ(C_L) ⟶ (Symⁿ C)_L` of `SymQuot/BaseChange/exists_symBaseChangeIso.lean`:

* `projOfBaseChange` — the `F`-point of `C` induced by an `F`-point of `C_L`;
* `pbPtEquiv` — the identification `X_L(F) ≃ X(F)` (`SymQuot/BaseChange/ptsBaseChange.lean`);
* `powMap_symBeta` (proved downstream) — β carries the sum of `x_0, …, x_{n-1}` (points of
  `C_L`) to the sum of the projections to `C`; this is the `powMap_βK` coherence used by area
  `BcDiv`.
-/
import Submission.Work.SymQuot.BaseChange.exists_symBaseChangeIso
import Submission.Work.SymQuot.BaseChange.ptsBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.SymQuot.BaseChange

/-- **The `F`-point of `C` induced by an `F`-point of `C_L`**, by projecting along the
base-change square. -/
noncomputable def projOfBaseChange {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {L : Type u} [Field L] [Algebra K L] {F : Type u} [Field F] [Algebra K F] [Algebra L F]
    [IsScalarTower K L F] (x : Work.SpecLin.FPt (C.baseChange L).toOver F) :
    Work.SpecLin.FPt C.toOver F :=
  Over.homMk (x.left ≫ (Work.CurveBasics.Curve.bcSquare C L).π) (by
    rw [Category.assoc, (Work.CurveBasics.Curve.bcSquare C L).isPullback.w]
    rw [← Category.assoc, Over.w x]
    change Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K F))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (algebraMap L F).comp (algebraMap K L) = algebraMap K F from
      (IsScalarTower.algebraMap_eq K L F).symm])

end Work.SymQuot.BaseChange
