/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv: transport of point divisors along an equality of indices

The divisor `SymQuot.DivOf.divOf F p` of a point of `Symⁿ C` does not depend on `n` *as a
divisor on `C_F`*: if `n = m` and `q` is a point of `Symⁿ C`, then the transported point
`q ≫ eqToHom (Symⁿ C = Symᵐ C)` has the same divisor.  This is used in the assembly
`Work.BcDiv.symBC` of the bundle `Work.Charts.SymBC`, where the two `RochData` are only linked
by `R'.g = R.g`.

## Main results

* `Work.BcDiv.divOf_eqToIso`.
-/
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.Sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.BcDiv

noncomputable section

/-- **Transport of `divOf` along an equality of indices.** -/
theorem divOf_eqToIso {K : Type u} [Field K] {C : Curve K} {n m : ℕ} [NeZero n] [NeZero m]
    [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F] (h : n = m)
    (q : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    Work.SymQuot.DivOf.divOf F
        (q ≫ (eqToIso (congrArg (fun k => Work.SymQuot.Sym C k) h)).hom)
      = Work.SymQuot.DivOf.divOf F q := by
  cases h
  simp

end

end Work.BcDiv
