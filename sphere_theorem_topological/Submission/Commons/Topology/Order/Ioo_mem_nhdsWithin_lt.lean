import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Topology.Order

open Filter Set
open scoped _root_.Topology

/-- `Ioo a b` is a neighbourhood of `b` from the left, for `a < b`.  Together with the mirrored
statement for `nhdsWithin a (Ioi a)` this is the standard "one-sided interval" membership fact. -/
theorem Ioo_mem_nhdsWithin_lt {a b : ℝ} (hab : a < b) : Ioo a b ∈ nhdsWithin b (Iio b) :=
  Ioo_mem_nhdsLT hab

end Commons.Topology.Order