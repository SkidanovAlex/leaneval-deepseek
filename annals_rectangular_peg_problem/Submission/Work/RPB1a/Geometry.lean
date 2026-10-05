import Mathlib
import Submission.Work.RPV.Defs

/-!
# RPB1a: the Jordan-curve predicate, library-free

The conformal-map route (`RECTPEG_B1_LEAD.md`) uses exactly one notion from the external TauCeti
library: `TauCeti.IsJordanCurve`, defined there as `Nonempty (C ≃ₜ Circle)`.  **That library cannot
be imported in this workspace** (`lakefile.toml` is fixed and does not `require` TauCeti, so
`import TauCeti.…` fails with `unknown module prefix 'TauCeti'`; see the machine-checked
`Submission/Work/RPB/B1a/IMPORT_BLOCKER.md` for the sibling subproject's finding).

This file restates the predicate under its own name, verbatim as a `def` whose body is the unfolded
form of TauCeti's definition, so that
* node statements `N4`/`N6` can be written and the whole assembly layer can be built without the
  library, and
* when TauCeti (or an in-house replacement) becomes available, the two predicates are
  *definitionally equal*, so bridging is `Iff.rfl`/`rfl` and no statement needs changing.

Everything else the route wanted from TauCeti (the Jordan separation / frontier facts, the homology
Cauchy theorem, the circle Schwarz reflection principle, the Carathéodory boundary correspondence)
is **not** restated here: it is exactly the content of the held nodes `N4`, `N5`, `N6`, `N7`, whose
proofs are blocked on the library decision.  The *statements* of those nodes are TauCeti-free
(`Nodes.lean`) and their proofs are the only place the library enters.
-/

set_option autoImplicit false

open Complex Set Metric
open scoped ContDiff Real

noncomputable section

namespace Work.RPB1a

/-- A subset of `ℂ` homeomorphic to the circle — the unfolded form of `TauCeti.IsJordanCurve`. -/
def IsJordanCurveSet (C : Set ℂ) : Prop := Nonempty (C ≃ₜ Circle)

lemma isJordanCurveSet_iff (C : Set ℂ) : IsJordanCurveSet C ↔ Nonempty (C ≃ₜ Circle) := Iff.rfl

end Work.RPB1a

end
