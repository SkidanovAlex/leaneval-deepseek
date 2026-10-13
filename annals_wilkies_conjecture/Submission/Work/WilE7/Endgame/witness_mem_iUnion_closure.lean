import Mathlib

namespace Work.WilE7.Endgame

/-- If a sequence `f` converges to `a` and every value `f t` lies in the (finite,
list-indexed) union `⋃ i ∈ L, g i`, then `a` lies in the union of the closures
`⋃ i ∈ L, closure (g i)`. -/
theorem witness_mem_iUnion_closure {α β : Type*} [TopologicalSpace α]
    {L : List β} {f : ℕ → α} {a : α} {g : β → Set α}
    (ht : Filter.Tendsto f Filter.atTop (nhds a))
    (hmem : ∀ t, f t ∈ ⋃ i ∈ L, g i) :
    a ∈ ⋃ i ∈ L, closure (g i) := by
  -- `a` is in the closure of the whole (finite) union.
  have hU : a ∈ closure (⋃ i ∈ L, g i) :=
    mem_closure_of_tendsto ht (Filter.Eventually.of_forall hmem)
  -- Each `g i` is contained in its closure.
  have hsub : (⋃ i ∈ L, g i) ⊆ (⋃ i ∈ L, closure (g i)) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hi, subset_closure hxi⟩
  -- A finite (list-indexed) union of closed sets is closed.
  have hclosed : IsClosed (⋃ i ∈ L, closure (g i)) := by
    have : ∀ M : List β, IsClosed (⋃ i ∈ M, closure (g i)) := by
      intro M
      induction M with
      | nil => simp
      | cons b M ih =>
        simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]
        exact isClosed_closure.union ih
    exact this L
  exact (closure_minimal hsub hclosed) hU

end Work.WilE7.Endgame
