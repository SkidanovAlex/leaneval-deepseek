import Mathlib

/-!
# A covering walk in a connected finite graph

Given a finite `Preconnected` simple graph `G` and a vertex `v₀`, there is a walk starting at `v₀`
which visits every vertex of `G`: enumerate the vertices and concatenate, for each new vertex, an
arbitrary walk from the current endpoint to it (which exists by connectedness).  This is the
combinatorial content of `Work.Smooth.SphereJordan.exists_walk_covering`.
-/

noncomputable section

namespace Work.Smooth.SphereJordan

/-- Auxiliary recursion: starting from a walk `p` ending at the current vertex `c`, given a list `l`
of vertices to be visited, extend `p` by walks to the successive vertices of `l`, retaining
everything already visited. -/
private def go {V : Type*} (G : SimpleGraph V) (w₀ : V) (hG : G.Preconnected) (c : V)
    (p : G.Walk w₀ c) : List V → Σ' c, G.Walk w₀ c
  | [] => ⟨c, p⟩
  | x :: xs => go G w₀ hG x (p.append (Classical.choice (hG c x))) xs

/-- Everything visited by `p`, and every vertex of the list `l`, is visited by `go G w₀ hG c p l`. -/
private theorem go_spec {V : Type*} (G : SimpleGraph V) (w₀ : V) (hG : G.Preconnected) :
    ∀ (c : V) (p : G.Walk w₀ c) (l : List V),
      p.support ⊆ (go G w₀ hG c p l).2.support ∧
        ∀ x ∈ l, x ∈ (go G w₀ hG c p l).2.support := by
  intro c p l
  induction l generalizing c p with
  | nil =>
      refine ⟨fun x hx => ?_, by simp⟩
      exact hx
  | cons y ys ih =>
      have key : go G w₀ hG c p (y :: ys)
          = go G w₀ hG y (p.append (Classical.choice (hG c y))) ys := rfl
      rw [key]
      obtain ⟨ih₁, ih₂⟩ := ih y (p.append (Classical.choice (hG c y)))
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · exact ih₁ (SimpleGraph.Walk.support_subset_support_append_left p _ hx)
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ih₁ (SimpleGraph.Walk.end_mem_support _)
        · exact ih₂ x hx

/-- **A connected finite graph has a walk visiting all its vertices.**  There are a natural number
`n` and a map `u : Fin (n + 1) → V` with `u 0 = v₀`, whose range is all of `V`, and such that
consecutive values of `u` are adjacent in `G`. -/
theorem walk_of_preconnected {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Preconnected) (v₀ : V) :
    ∃ (n : ℕ) (u : Fin (n + 1) → V), u 0 = v₀ ∧ (∀ x : V, ∃ i, u i = x) ∧
      (∀ i : Fin n, G.Adj (u i.castSucc) (u i.succ)) := by
  classical
  let l : List V := (Finset.univ : Finset V).toList
  have hl : ∀ x : V, x ∈ l := by
    intro x
    rw [Finset.mem_toList]
    exact Finset.mem_univ x
  set W := (go G v₀ hG v₀ (SimpleGraph.Walk.nil) l).2 with hW
  have hspec : ∀ x ∈ l, x ∈ W.support := by
    intro x hx
    have h' := (go_spec G v₀ hG v₀ (SimpleGraph.Walk.nil) l).2 x hx
    simpa only [hW] using h'
  refine ⟨W.length, fun i => W.getVert (i : ℕ), ?_, ?_, ?_⟩
  · simp
  · intro x
    have hx : x ∈ W.support := hspec x (hl x)
    refine ⟨⟨W.support.idxOf x, ?_⟩, ?_⟩
    · have hlt := List.idxOf_lt_length_of_mem hx
      rw [SimpleGraph.Walk.length_support] at hlt
      omega
    · exact SimpleGraph.Walk.getVert_support_idxOf W hx
  · intro i
    exact W.adj_getVert_succ i.isLt

end Work.Smooth.SphereJordan
