/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `SymGeom C n` structure on `Symⁿ C`, conditional on `divOf_complete` (area SY)

`Work.SpecLin.SymGeom C n` is the interface through which area `PR` consumes area `SY`.  Every
field of it is now available on `S = Sym C n` *except* `divOf_complete` (that a point exists over
every effective divisor of degree `n`, `DivOf/Complete/divOf_complete.lean`).  This file assembles
the whole instance from a proof of that single remaining statement, so that as soon as
`divOf_complete` is proved the instance is

```
noncomputable instance : SpecLin.SymGeom C n := symGeomOfComplete divOf_complete
```

The `DivBase` argument of `SymGeom` is deliberately *not* a variable here: it must be resolved by
instance search to `Work.SymQuot.instDivBase` (`DivBaseInst.lean`), which is the realisation of
`bc` against which `divOf_map` is proved.
-/
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.isProper_sym
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.divOf_deg
import Submission.Work.SymQuot.DivOf.divOf_injective
import Submission.Work.SymQuot.DivOf.divOf_map
import Submission.Work.SymQuot.DivOf.divOf_powMapC1
import Submission.Work.SymQuot.DivOf.Complete.exists_ptDiv_sum_of_div
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SpecLin.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option warn.classDefReducibility false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

/-- **The `SymGeom C n` structure on `Symⁿ C`**, from a proof of `divOf_complete`. -/
noncomputable def symGeomOfComplete {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} [NeZero n]
    (hcomplete : ∀ {F : Type u} [Field F] [Algebra K F] (D : Work.SpecLin.Dv C F),
      D.IsEffective → (C.baseChange F).deg D = n →
        ∃ p : Work.SpecLin.FPt (Sym C n) F, DivOf.divOf F p = D) :
    Work.SpecLin.SymGeom C n where
  S := Sym C n
  isProper := Sym.isProper_sym C n
  divOf := fun {F} _ _ p => DivOf.divOf F p
  divOf_injective := fun {F} _ _ p q h => DivOf.divOf_injective p q h
  divOf_isEffective := fun {F} _ _ p => DivOf.divOf_isEffective p
  divOf_deg := fun {F} _ _ p => DivOf.divOf_deg p
  divOf_complete := fun {F} _ _ D hD hdeg => hcomplete D hD hdeg
  divOf_map := fun {F F'} _ _ _ _ e p => DivOf.divOf_map e p
  powMap := fun {T} x => Sym.powMap C n x
  powMap_comp := fun {T T'} g x => Sym.powMap_comp C n g x
  divOf_powMap := fun {F} _ _ x => DivOf.divOf_powMapC1 x
  split := fun {F F'} _ _ _ _ _ _ _ D hD hdeg =>
    DivOf.Complete.exists_ptDiv_sum_of_div D hD hdeg

end Work.SymQuot
