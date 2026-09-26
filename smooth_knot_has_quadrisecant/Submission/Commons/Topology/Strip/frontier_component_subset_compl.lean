import Mathlib

/-!
# The frontier of a component of an open set

A reusable point-set tool: if `O` is open in a locally connected space and `E` is the connected
component of `O` through `z ∈ O`, then `frontier E ⊆ Oᶜ`.

Used (in `Topology/Strip/component_meets_inter_of_no_translate_path`) to prove that a connected
component of one of two `T`-invariant open-in-a-strip sets that avoids the other set must be
*closed* in the plane, whence clopen in the connected strip.
-/

open Set

namespace Commons.Topology.Strip

/-- **The frontier of a component of an open set is disjoint from the open set.** -/
theorem frontier_component_subset_compl {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {O : Set X} (hO : IsOpen O) {z : X} (hz : z ∈ O) :
    frontier (connectedComponentIn O z) ⊆ Oᶜ := by
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpO
  have hpcl : p ∈ closure (connectedComponentIn O z) := hp.1
  have hpre : IsPreconnected (connectedComponentIn O z ∪ {p}) := by
    refine isPreconnected_connectedComponentIn.subset_closure (fun x hx => Or.inl hx) ?_
    intro x hx
    rcases hx with h | rfl
    · exact subset_closure h
    · exact hpcl
  have hsub : connectedComponentIn O z ∪ {p} ⊆ O := by
    rintro x (hx | rfl)
    · exact connectedComponentIn_subset O z hx
    · exact hpO
  have hzE : z ∈ connectedComponentIn O z := mem_connectedComponentIn hz
  have hpE : p ∈ connectedComponentIn O z :=
    hpre.subset_connectedComponentIn (Or.inl hzE) hsub (Or.inr rfl)
  have hEopen : IsOpen (connectedComponentIn O z) := hO.connectedComponentIn
  have hpint : p ∈ interior (connectedComponentIn O z) := by
    rw [hEopen.interior_eq]; exact hpE
  exact (Set.disjoint_left.mp disjoint_interior_frontier hpint) hp

end Commons.Topology.Strip
