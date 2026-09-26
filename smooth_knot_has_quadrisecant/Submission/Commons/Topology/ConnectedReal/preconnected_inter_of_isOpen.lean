import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace Commons.Topology.ConnectedReal

/-- In `ℝ`, an open preconnected set is an interval (`OrdConnected`), so the intersection of two
open preconnected sets, being the intersection of two intervals, is again an interval, hence
preconnected. -/
lemma preconnected_inter_of_isOpen {s t : Set ℝ}
    (hs_open : IsOpen s) (ht_open : IsOpen t)
    (hs : IsPreconnected s) (ht : IsPreconnected t)
    (hne : (s ∩ t).Nonempty) : IsPreconnected (s ∩ t) := by
  rw [isPreconnected_iff_ordConnected]
  exact Set.OrdConnected.inter (isPreconnected_iff_ordConnected.mp hs)
    (isPreconnected_iff_ordConnected.mp ht)

end Commons.Topology.ConnectedReal