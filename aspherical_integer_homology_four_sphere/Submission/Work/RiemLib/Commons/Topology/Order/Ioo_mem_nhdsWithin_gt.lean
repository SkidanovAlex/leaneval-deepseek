import Mathlib.Analysis.Normed.Order.Lattice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Order

open Filter Set
open scoped Topology

/-- `Ioo a b` is a neighbourhood of `a` from the right, for `a < b` (companion of
`Ioo_mem_nhdsWithin_lt`). -/
theorem Ioo_mem_nhdsWithin_gt {a b : ℝ} (hab : a < b) : Ioo a b ∈ nhdsWithin a (Ioi a) :=
  Ioo_mem_nhdsGT hab

end Commons.Topology.Order