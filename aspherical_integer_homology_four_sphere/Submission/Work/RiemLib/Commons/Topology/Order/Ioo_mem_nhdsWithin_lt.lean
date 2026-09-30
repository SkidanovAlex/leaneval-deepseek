import Mathlib.Analysis.Normed.Order.Lattice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Order

open Filter Set
open scoped _root_.Topology

/-- `Ioo a b` is a neighbourhood of `b` from the left, for `a < b`.  Together with the mirrored
statement for `nhdsWithin a (Ioi a)` this is the standard "one-sided interval" membership fact. -/
theorem Ioo_mem_nhdsWithin_lt {a b : ℝ} (hab : a < b) : Ioo a b ∈ nhdsWithin b (Iio b) :=
  Ioo_mem_nhdsLT hab

end Commons.Topology.Order