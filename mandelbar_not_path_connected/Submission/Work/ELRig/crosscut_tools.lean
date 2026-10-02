/-
# Re-export of the plane-Jordan crosscut tools used by the crossing-symmetry lemmas.

`Submission/Work/ELRig/crossing_of_zero_arc.lean` needs the two halves of the statement
"a crosscut of a disc separates it": `crosscut_complement_at_most_two` (any three points of the
disc minus the crosscut: two of them lie in the same connected component) and
`crosscut_complement_not_preconnected` (the complement is not connected, hence there are exactly
two components).  Both live outside `Submission/Work/`, so they are gathered here in a module of
`Submission/Work/ELRig/` that can be listed in `depends_on`.
-/
import Mathlib
import Submission.Commons.Topology.Jordan.crosscut_complement_at_most_two
import Submission.Commons.Topology.Jordan.crosscut_complement_not_preconnected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

