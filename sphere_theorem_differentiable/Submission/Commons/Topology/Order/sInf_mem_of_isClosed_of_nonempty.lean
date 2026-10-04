import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Monotone

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Order

theorem sInf_mem_of_isClosed_of_nonempty {s : Set ℝ} (hs : IsClosed s) (hne : s.Nonempty)
    (hbdd : BddBelow s) : sInf s ∈ s :=
  hs.csInf_mem hne hbdd

end Commons.Topology.Order