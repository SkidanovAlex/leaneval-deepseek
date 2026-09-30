/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RR8: the pullback of a canonical divisor is canonical

Canonicality is characterised numerically (`Work.RiemannRoch.Canonical.isCanonical_iff`):
`W` is canonical iff `deg W = 2g - 2` and `l W = g`.  Both quantities are invariant under base
change (`RR8.deg_divMap`, `RR8.genus_eq`, and the hypothesis `hl` that `l` is invariant), so the
pullback `S.divMap W` of a canonical divisor is again canonical.  This is the form in which GC
uses the canonical class of a base-changed curve.
-/
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.Canonical.isCanonical_iff
import Submission.Work.RiemannRoch.RR8.deg_divMap
import Submission.Work.RiemannRoch.RR8.genus_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.RiemannRoch.RR8

open Work.CurveBasics

universe u

/-- **RR8**: the pullback of a canonical divisor along a base-change square is canonical. -/
theorem isCanonical_divMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Work.CurveBasics.Curve k} {C' : Work.CurveBasics.Curve F}
    (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) {W : C.Div}
    (hW : Work.RiemannRoch.Curve.IsCanonical C W) :
    Work.RiemannRoch.Curve.IsCanonical C' (S.divMap W) := by
  rw [Work.RiemannRoch.Canonical.isCanonical_iff]
  refine ⟨?_, ?_⟩
  · rw [deg_divMap S hl W, hW.deg, genus_eq S hl]
  · rw [hl W, hW.l_eq, genus_eq S hl]

end Work.RiemannRoch.RR8
