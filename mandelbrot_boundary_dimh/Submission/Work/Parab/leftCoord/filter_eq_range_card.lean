import Mathlib

namespace Work.Parab.leftCoord

/-- If `p` is downward closed on `{0, ..., k-1}` (i.e. `p j` with `j < k` forces
`p i` for all `i < j`), then the set of `j < k` satisfying `p` is an initial
segment of `ℕ`, hence equals `range` of its own cardinality. -/
theorem filter_eq_range_card {k : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (h : ∀ j < k, p j → ∀ i, i < j → p i) :
    (Finset.range k).filter p = Finset.range ((Finset.range k).filter p).card := by
  set s := (Finset.range k).filter p with hs
  -- `s` is downward closed
  have hdown : ∀ {j : ℕ}, j ∈ s → ∀ i, i < j → i ∈ s := by
    intro j hj i hij
    rw [hs, Finset.mem_filter] at hj
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (lt_trans hij (Finset.mem_range.mp hj.1)),
      h j (Finset.mem_range.mp hj.1) hj.2 i hij⟩
  ext n
  rw [Finset.mem_range]
  constructor
  · -- `n ∈ s` forces every `i ≤ n` into `s`, so `n + 1 ≤ s.card`
    intro hn
    have hsub : Finset.range (n + 1) ⊆ s := by
      intro i hi
      rw [Finset.mem_range] at hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h' | rfl
      · exact hdown hn i h'
      · exact hn
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    omega
  · -- if `n ∉ s`, downward closure makes `s ⊆ range n`, so `s.card ≤ n`
    intro hn
    by_contra hns
    have hsub : s ⊆ Finset.range n := by
      intro i hi
      rw [Finset.mem_range]
      by_contra hlt
      push Not at hlt
      rcases Nat.lt_or_eq_of_le hlt with h' | rfl
      · exact hns (hdown hi n h')
      · exact hns hi
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    omega

end Work.Parab.leftCoord
