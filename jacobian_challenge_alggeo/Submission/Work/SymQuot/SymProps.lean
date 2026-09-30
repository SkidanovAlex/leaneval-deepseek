/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `SymProps` for `Symⁿ C` (area SY)

Area `CH` (`Submission/Work/Charts/Basic.lean`) collects the geometry of `Symⁿ C` that it consumes
in the structure `Work.Charts.SymProps C n` (`IsIntegral`, `GeometricallyIrreducible`,
`LocallyOfFiniteType`, `QuasiCompact`).  All four are proved in area SY for
`S = Work.SymQuot.Sym C n` (`Sym/isIntegral_sym.lean`, `Sym/geometricallyIrreducible_sym.lean`,
`Sym/locallyOfFiniteType_sym.lean`, `Sym/quasiCompact_sym.lean`), so the structure is inhabited
for the instance of `SymGeom C n` built in `SymGeomInst.lean`.
-/
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.SymQuot.Sym.geometricallyIrreducible_sym
import Submission.Work.SymQuot.Sym.locallyOfFiniteType_sym
import Submission.Work.SymQuot.Sym.quasiCompact_sym
import Submission.Work.Charts.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Charts

/-- **The geometry of `Symⁿ C` consumed by area `CH`**, for `n ≥ 1`. -/
noncomputable instance instSymProps {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    [NeZero n] [Work.SymQuot.CurveAffineCover C] : SymProps C n where
  isIntegral := Work.SymQuot.Sym.isIntegral_sym C n
  geometricallyIrreducible := Work.SymQuot.Sym.geometricallyIrreducible_sym C n
  locallyOfFiniteType := Work.SymQuot.Sym.locallyOfFiniteType_sym C n
  quasiCompact := Work.SymQuot.Sym.quasiCompact_sym C n

end Work.Charts
