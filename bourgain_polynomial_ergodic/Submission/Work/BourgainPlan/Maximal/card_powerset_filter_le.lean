import Mathlib

namespace Work.BourgainPlan.Maximal

/-- The number of subsets of a finite set `s` of cardinality at most `k` is at most `(k + 1) * (|s| + 1) ^ k`.  (Proof route: the filtered powerset is contained in the union of the `powersetCard i`, `i ≤ k`; `#(powersetCard i s) = (s.card).choose i ≤ s.card ^ i ≤ (s.card + 1) ^ k`.) -/
theorem card_powerset_filter_le {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ) :
    (s.powerset.filter (fun A => A.card ≤ k)).card ≤ (k + 1) * (s.card + 1) ^ k := by
  -- Every set in the filtered powerset has size `i ≤ k`, hence lies in `powersetCard i s`.
  have hsub : s.powerset.filter (fun A => A.card ≤ k)
      ⊆ (Finset.range (k + 1)).biUnion (fun i => s.powersetCard i) := by
    intro A hA
    rw [Finset.mem_filter] at hA
    obtain ⟨hApow, hAcard⟩ := hA
    rw [Finset.mem_biUnion]
    exact ⟨A.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hAcard),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hApow, rfl⟩⟩
  calc (s.powerset.filter (fun A => A.card ≤ k)).card
      ≤ ((Finset.range (k + 1)).biUnion (fun i => s.powersetCard i)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (k + 1), (s.powersetCard i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (k + 1), s.card.choose i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.card_powersetCard]
    _ ≤ ∑ _i ∈ Finset.range (k + 1), (s.card + 1) ^ k := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        calc s.card.choose i ≤ s.card ^ i := Nat.choose_le_pow _ _
          _ ≤ (s.card + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ s.card) i
          _ ≤ (s.card + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos s.card) hik
    _ = (k + 1) * (s.card + 1) ^ k := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Work.BourgainPlan.Maximal
