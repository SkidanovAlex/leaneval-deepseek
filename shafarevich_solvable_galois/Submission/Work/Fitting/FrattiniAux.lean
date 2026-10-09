/-
Copyright (c) 2025. All rights reserved.

# Elementary facts about the Frattini subgroup

The Frattini subgroup `Φ(G) = frattini G` is the intersection of the maximal (`IsCoatom`)
subgroups.  For a finite group the subgroup lattice is coatomic, and we record the immediate
consequences used throughout this area:

* `le_frattini_iff` : `N ≤ Φ(G)` iff `N` is contained in every maximal subgroup;
* `exists_coatom_ge` : every proper subgroup is contained in a maximal subgroup.
-/
import Mathlib
import Submission.Work.Fitting.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

set_option maxHeartbeats 1000000
open scoped Classical
open Subgroup

variable {G : Type*} [Group G]

/-- The subgroup lattice of a finite group is coatomic: every proper subgroup is contained in a
maximal one. -/
theorem isCoatomic_subgroup (G : Type*) [Group G] [Finite G] : IsCoatomic (Subgroup G) :=
  inferInstance

/-- Every proper subgroup is contained in a maximal subgroup. -/
theorem exists_coatom_ge [Finite G] (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ K : Subgroup G, IsCoatom K ∧ H ≤ K := by
  rcases IsCoatomic.eq_top_or_exists_le_coatom H with h | h
  · exact absurd h hH
  · exact h

/-- `Φ(G)` is the intersection of the maximal subgroups. -/
theorem le_frattini_iff {N : Subgroup G} :
    N ≤ frattini G ↔ ∀ K : Subgroup G, IsCoatom K → N ≤ K := by
  rw [frattini, Order.radical]
  simp only [le_iInf_iff, Set.mem_ofPred_eq]

end Work.Fitting
