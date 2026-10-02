/-
# The escape set of the tricorn is preconnected

The escape set (basin of infinity) of the tricorn

`EscapeSet c = {z : ℂ | 0 < G_c z}`

is the set of points whose orbit under `T_c(w) = conj w ^ 2 + c` escapes to infinity
(`Work.Bottcher.Green.green_pos_iff`).  That is precisely the *escaping set*
`Work.ParamRays.escapingSet c` of the parameter-ray chapter, whose preconnectedness is
already established there (`Work.ParamRays.isPreconnected_escapingSet`) by writing it as
the increasing union of the entire-coercive superlevel sets
`{z | escR c < ‖T_c^[2n] z‖}` and applying the maximum-modulus principle.

Here we only have to bridge the two vocabularies: the escaping set is *defined* by the
divergence of the orbit norms, so the bridge is definitional.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.ParamRays.isDynBottcher_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction


/-- The escape set of `Work.Bottcher` is the escaping set of `Work.ParamRays`: both consist
of the points whose `T_c`-orbit tends to infinity.  The identification is the positivity
criterion for the Green function (`Work.Bottcher.Green.green_pos_iff`) together with the
definition of `Work.ParamRays.Escaping`. -/
theorem escapeSet_eq_escapingSet (c : ℂ) :
    Work.Bottcher.EscapeSet c = Work.ParamRays.escapingSet c := by
  ext z
  rw [Work.Bottcher.mem_EscapeSet, Work.Bottcher.Green.green_pos_iff,
    Work.ParamRays.mem_escapingSet]
  rfl

theorem isPreconnected_escapeSet (c : ℂ) : IsPreconnected (Work.Bottcher.EscapeSet c) := by
  rw [escapeSet_eq_escapingSet c]
  exact Work.ParamRays.isPreconnected_escapingSet c

end Work.Bottcher.Contraction
