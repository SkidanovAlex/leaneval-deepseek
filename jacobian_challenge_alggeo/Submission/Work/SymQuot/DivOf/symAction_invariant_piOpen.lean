import Mathlib
import Submission.Work.SymQuot.DivOf.Setup
import Submission.Work.SymQuot.ProdOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf

theorem symAction_invariant_piOpen {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) (V : C.left.Opens) : (Work.SymQuot.symAction C n).IsInvariantOpen (Work.SymQuot.piOpen C.toOver V n) :=
  fun σ => Work.SymQuot.piOpen_invariant C.toOver V n σ.down

end Work.SymQuot.DivOf
