import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.spread_chain_nesting_saturated

namespace Work.Horn

/-- **Item 2(c): from the chain to the spread `B i = ⋃_n W n i`** (`NOTES_GERM_F0.md` §46).

`G` is holomorphic on the open `D`; `V` are the petals; `W` is an increasing chain of open,
connected subsets of `D` with `W 0 i = V i`, `G '' W (n+1) i ⊆ W n i ∪ {0}`, and `G` mapping the
petals forward into themselves modulo `0` with `0 ∉ V i`.

Conclusion: the unions `B i := ⋃_n W n i` are open, connected, contained in `D`, contain their
petals, and are forward invariant modulo `0` (`G '' B i ⊆ B i ∪ {0}`).

Suggested proof: open is an arbitrary union; connected is `IsConnected.iUnion_of_chain`
(monotonicity plus `IsConnected.nonempty` give nonempty successive intersections); `V i ⊆ ⋃` from
`hW0`; `⋃ ⊆ D` from `hWsub`; invariance by cases: for `z ∈ W 0 i` use `hVmap` with `hW0`, and for
`z ∈ W (m+1) i` apply `hWmap m i` (its target already sits in `B i ∪ {0}`).

This is the elementary half of the passage to the spreads — everything except the two clauses that
§45 established are *not* derivable here (maximality among preconnected subsets of the basin, and
properness of `G : B i → B i`), which belong to the interface object of §43/§46.  Deliberately no
`IsImmediateBasin`, no `B i ⊆ G '' B i` and no simple connectivity is claimed. -/
theorem spread_union_basic {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    {W : ℕ → Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hWopen : ∀ n i, IsOpen (W n i)) (hWconn : ∀ n i, IsConnected (W n i))
    (hWsub : ∀ n i, W n i ⊆ D) (hW0 : ∀ i, W 0 i = V i)
    (hWmono : ∀ n i, W n i ⊆ W (n + 1) i)
    (hWmap : ∀ n i, Set.MapsTo G (W (n + 1) i) (W n i ∪ {0}))
    (hVmap : ∀ i, ∀ z ∈ V i, G z ∈ V i ∪ {0})
    (hVne : ∀ i, (0 : ℂ) ∉ V i) :
    (∀ i, IsOpen (⋃ n, W n i)) ∧
      (∀ i, IsConnected (⋃ n, W n i)) ∧
      (∀ i, V i ⊆ ⋃ n, W n i) ∧
      (∀ i, (⋃ n, W n i) ⊆ D) ∧
      (∀ i, ∀ z ∈ ⋃ n, W n i, G z ∈ (⋃ n, W n i) ∪ {0}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- arbitrary union of open sets
    intro i
    exact isOpen_iUnion (fun n => hWopen n i)
  · -- an increasing union of connected sets is connected: consecutive terms meet because
    -- each `W n i` is nonempty and `W n i ⊆ W (n+1) i`
    intro i
    refine IsConnected.iUnion_of_chain (s := fun n => W n i) (fun n => hWconn n i) ?_
    intro n
    obtain ⟨x, hx⟩ := (hWconn n i).nonempty
    exact ⟨x, hx, hWmono n i hx⟩
  · -- the petals sit in the union through `W 0 i = V i`
    intro i z hz
    exact Set.mem_iUnion.mpr ⟨0, (hW0 i).symm ▸ hz⟩
  · -- everything stays inside `D`
    intro i z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact hWsub n i hn
  · -- forward invariance modulo `0`, by cases on the level
    intro i z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    rcases n with _ | m
    · -- level `0`: `W 0 i = V i`, use the petal hypothesis
      rw [hW0 i] at hn
      rcases hVmap i z hn with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨0, (hW0 i).symm ▸ h⟩)
      · exact Or.inr h
    · -- level `m + 1`: use the chain map, whose target is `W m i ∪ {0} ⊆ B i ∪ {0}`
      rcases hWmap m i hn with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨m, h⟩)
      · exact Or.inr h

end Work.Horn
