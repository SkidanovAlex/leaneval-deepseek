import Mathlib.Data.Setoid.Partition
import Mathlib.Order.CompletePartialOrder

namespace Commons.Data.Finset

theorem prod_eq_prod_of_isPartition {α M : Type*} [Fintype α] [DecidableEq α] [CommMonoid M]
    {s : Set (Set α)} (hs : Setoid.IsPartition s) (hfin : s.Finite) (F : α → M) :
    ∏ a : α, F a
      = ∏ C ∈ hfin.toFinset, ∏ a ∈ (Set.Finite.toFinset (Set.toFinite (C : Set α))), F a := by
  classical
  have hdisj : (↑hfin.toFinset : Set (Set α)).PairwiseDisjoint
      (fun C => Set.Finite.toFinset (Set.toFinite (C : Set α))) := by
    rw [Set.Finite.coe_toFinset hfin]
    intro C hC C' hC' hne
    change Disjoint (Set.Finite.toFinset (Set.toFinite (C : Set α)))
      (Set.Finite.toFinset (Set.toFinite (C' : Set α)))
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hxC : x ∈ C := (Set.Finite.mem_toFinset (Set.toFinite (C : Set α))).mp hx
    have hxC' : x ∈ C' := (Set.Finite.mem_toFinset (Set.toFinite (C' : Set α))).mp hx'
    have hdisC : Disjoint C C' := hs.pairwiseDisjoint hC hC' hne
    exact (Set.disjoint_left.mp hdisC hxC) hxC'
  have hbU : hfin.toFinset.biUnion (fun C => Set.Finite.toFinset (Set.toFinite (C : Set α)))
      = Finset.univ := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨C, -, -⟩
      exact Finset.mem_univ x
    · intro _
      obtain ⟨C, hCs, hxC⟩ := (hs.2 x).exists
      exact ⟨C, (Set.Finite.mem_toFinset hfin).mpr hCs,
        (Set.Finite.mem_toFinset (Set.toFinite (C : Set α))).mpr hxC⟩
  rw [← Finset.prod_biUnion (s := hfin.toFinset) (f := F) hdisj, hbU]

end Commons.Data.Finset