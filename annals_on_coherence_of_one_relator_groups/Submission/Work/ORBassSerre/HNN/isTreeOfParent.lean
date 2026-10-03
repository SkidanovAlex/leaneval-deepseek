import Mathlib

namespace Work.ORBassSerre.HNN

/-- If every vertex different from `base` has a neighbour one level below it (in the sense of
`N : V → ℕ`), then every vertex reaches `base`: descend repeatedly, `N` strictly decreases. -/
lemma reachable_base_of_hex {V : Type*} (G : SimpleGraph V) (N : V → ℕ) (base : V)
    (hex : ∀ X, X ≠ base → ∃ Y, G.Adj X Y ∧ N Y + 1 = N X) :
    ∀ X, G.Reachable X base := by
  intro X
  have key : ∀ n, ∀ X : V, N X = n → G.Reachable X base := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hXn
      by_cases hX : X = base
      · subst hX; exact SimpleGraph.Reachable.refl _
      · obtain ⟨Y, hXY, hYX⟩ := hex X hX
        have hlt : N Y < n := by omega
        obtain ⟨w⟩ := ih (N Y) hlt Y rfl
        exact ⟨SimpleGraph.Walk.cons hXY w⟩
  exact key (N X) X rfl

/-- The graph is acyclic.  If `c` were a cycle, take a vertex `X` of the cycle whose level is
maximal; rotating `c` to start at `X`, the two neighbours of `X` on the cycle are both one level
below `X`, so the uniqueness hypothesis forces them to be equal, contradicting
`Walk.IsCycle.snd_ne_penultimate`. -/
lemma isAcyclic_of_sep_of_parent {V : Type*} (G : SimpleGraph V) (N : V → ℕ)
    (hsep : ∀ X Y, G.Adj X Y → N Y = N X + 1 ∨ N X = N Y + 1)
    (huniq : ∀ X Y Z, G.Adj X Y → G.Adj X Z → N Y + 1 = N X → N Z + 1 = N X → Y = Z) :
    G.IsAcyclic := by
  classical
  intro v c hc
  have hne : c.support.toFinset.Nonempty :=
    ⟨v, by rw [List.mem_toFinset]; exact c.start_mem_support⟩
  obtain ⟨X, hXmem, hXmax⟩ := Finset.exists_max_image c.support.toFinset N hne
  rw [List.mem_toFinset] at hXmem
  have hXmax' : ∀ Y ∈ c.support, N Y ≤ N X := by
    intro Y hY
    exact hXmax Y (List.mem_toFinset.mpr hY)
  have hcyc : (c.rotate X hXmem).IsCycle := hc.rotate hXmem
  have hnil : ¬ (c.rotate X hXmem).Nil := hcyc.not_nil
  have hsnd_supp : (c.rotate X hXmem).snd ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c X hXmem).mp
      (List.tail_subset _ ((c.rotate X hXmem).snd_mem_tail_support hnil))
  have hpen_supp : (c.rotate X hXmem).penultimate ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c X hXmem).mp
      (List.dropLast_subset _ ((c.rotate X hXmem).penultimate_mem_dropLast_support hnil))
  have h1 : N (c.rotate X hXmem).snd + 1 = N X := by
    rcases hsep X _ ((c.rotate X hXmem).adj_snd hnil) with h | h
    · have := hXmax' _ hsnd_supp; omega
    · exact h.symm
  have h2 : N (c.rotate X hXmem).penultimate + 1 = N X := by
    rcases hsep _ X ((c.rotate X hXmem).adj_penultimate hnil) with h | h
    · exact h.symm
    · have := hXmax' _ hpen_supp; omega
  exact hcyc.snd_ne_penultimate (huniq X _ _
    ((c.rotate X hXmem).adj_snd hnil)
    (((c.rotate X hXmem).adj_penultimate hnil).symm) h1 h2)

/-- Given a height function `N` on a graph `G`, a base vertex, and the hypotheses that adjacent
vertices have levels differing by exactly one, that each non-base vertex has a *unique* neighbour
one level below it, that each non-base vertex has such a neighbour, and that level `0` is exactly
`base`, the graph `G` is a tree. -/
theorem isTreeOfParent {V : Type*} (G : SimpleGraph V) (N : V → ℕ) (base : V)
    (hsep : ∀ X Y, G.Adj X Y → N Y = N X + 1 ∨ N X = N Y + 1)
    (huniq : ∀ X Y Z, G.Adj X Y → G.Adj X Z → N Y + 1 = N X → N Z + 1 = N X → Y = Z)
    (hex : ∀ X, X ≠ base → ∃ Y, G.Adj X Y ∧ N Y + 1 = N X)
    (hbase : ∀ X, N X = 0 ↔ X = base) :
    G.IsTree := by
  exact @SimpleGraph.IsTree.mk V G
    (@SimpleGraph.Connected.mk V G
      (fun u v => (reachable_base_of_hex G N base hex u).trans
        (reachable_base_of_hex G N base hex v).symm) ⟨base⟩)
    (isAcyclic_of_sep_of_parent G N hsep huniq)

end Work.ORBassSerre.HNN
