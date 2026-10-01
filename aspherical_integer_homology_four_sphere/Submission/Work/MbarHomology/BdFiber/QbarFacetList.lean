/-
# The facet lists of `Q̄` as literal lists (generated)

Generated from `Submission/Work/MbarHomology/Data/QbarFacet.lean`: for each of the `865`
faces `x` of `Q̄`, `qFacetL x` is the list of the facets of `x`, in the order in which they
appear in the literal `Finset` of `qFacet x`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.AtlasCocycle
import Submission.Work.MbarHomology.Qbar.QbarFacetListCore

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

