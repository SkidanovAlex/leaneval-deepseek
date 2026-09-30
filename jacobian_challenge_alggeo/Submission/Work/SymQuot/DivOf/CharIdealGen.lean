/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic (characteristic-free) generators of the divisor ideal of a point of `Symⁿ C`

The *definitions* live in `Submission/Work/SymQuot/DivOf/GenCharpoly.lean` (the generic
characteristic polynomial) and `Submission/Work/SymQuot/DivOf/CharIdealGenDefs.lean`
(`ChartPt.genCharpolyValue`, `ChartPt.genGenerator`, `charIdealGen`); this module re-exports the
first, for compatibility with the path requested by the lead
(`Submission/Work/NOTES_LEAD_jacobian_divof.md` §1.2).

The point of the generic generators (as opposed to the `charIdeal` generators `χ_b(b)`,
`b ∈ Γ(C,V)`) is that the *existence* of a separating uniformising section `b` over the
(possibly finite) base field `K` is delicate, whereas the corresponding statement for the
generic element `∑_i X_i b_i` is a plain CRT argument over the field where the lift lives.
-/
import Submission.Work.SymQuot.DivOf.GenCharpoly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

