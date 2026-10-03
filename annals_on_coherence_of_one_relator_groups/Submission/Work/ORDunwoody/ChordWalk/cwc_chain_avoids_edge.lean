/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# A chain of a forest that avoids an edge is one-sided

`Work.ORDunwoody.eq_of_walk_avoids_edge` is the *walk* form of the fact that an edge of a forest is a
bridge: a walk that never traverses `s(a,b)` cannot join the two ends of `s(a,b)`.  The boundary
walks of the faces of the Dunwoody resolution are naturally given as *lists* of vertices (the
`wordSteps` of `ChordWalk/Defs.lean`), so here we prove the corresponding statement for a list
`γ` that is a *chain* (`γ.IsChain (fun x y => x = y ∨ T.Adj x y)`): if it starts at one end of the
edge `s(a,b)`, ends at the other, and never makes the jump `s(a,b)`, then those two ends coincide.

The two ingredients are

* `reachable_of_isChain_of_forall`: a chain whose every step is a `G`-reachability gives a
  `G`-reachability between its head and its last element;
* `reachable_deleteEdges_of_chain`: applied to `G = T.deleteEdges {s(a,b)}`, this turns a chain
  that avoids `s(a,b)` into a reachability in the graph with `s(a,b)` removed.

The result then follows from `SimpleGraph.isBridge_iff` and
`SimpleGraph.isAcyclic_iff_forall_adj_isBridge`.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Work.ORDunwoody.ChordWalk

/-- A list that is a chain with respect to a relation `r`, each step of which implies `G`-reachability
of its two ends, has its head `G`-reachable from its last element. -/
lemma reachable_of_isChain_of_forall {V : Type*} (G : SimpleGraph V)
    (r : V → V → Prop) (hr : ∀ x y, r x y → G.Reachable x y) :
    ∀ (l : List V) (b c : V), l.IsChain r → l.head? = some b → l.getLast? = some c →
      G.Reachable b c := by
  intro l
  induction l with
  | nil => intro b c _ hb _; simp at hb
  | cons x rest ih =>
      intro b c hchain hb hc
      simp only [List.head?_cons, Option.some.injEq] at hb
      rw [← hb]
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hc
          rw [← hc]
      | cons y rest' =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨hxy, hchain'⟩ := hchain
          have hc' : (y :: rest').getLast? = some c := by simpa using hc
          exact (hr x y hxy).trans (ih (b := y) (c := c) hchain' rfl hc')

/-- A chain of `T`, whose consecutive *distinct* pairs are never `s(a,b)`, is a chain all of whose
steps are `T.deleteEdges {s(a,b)}`-paths (equal steps being trivial); in particular its head can be
reached from its last element after deleting the edge `s(a,b)`. -/
lemma reachable_deleteEdges_of_chain {V : Type*} (T : SimpleGraph V)
    (a b : V) (γ : List V)
    (hchain : γ.IsChain (fun x y => x = y ∨ T.Adj x y))
    (havoid : ∀ (i : ℕ) (x y : V), γ[i]? = some x → γ[i + 1]? = some y → x ≠ y →
      Sym2.mk x y ≠ Sym2.mk a b)
    {b' c : V} (hhead : γ.head? = some b') (hlast : γ.getLast? = some c) :
    (T.deleteEdges {Sym2.mk a b}).Reachable b' c := by
  refine reachable_of_isChain_of_forall (T.deleteEdges {Sym2.mk a b})
    (fun x y => x = y ∨ (T.Adj x y ∧ Sym2.mk x y ≠ Sym2.mk a b)) ?_ γ b' c ?_ hhead hlast
  · intro x y h
    rcases h with h | ⟨h, hne⟩
    · subst h; exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.deleteEdges_adj.mpr ⟨h, by simpa using hne⟩).reachable
  · rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro x y l₁ l₂ heq
    have hxy := (List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain) heq
    rcases hxy with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      have hi : γ[l₁.length]? = some x := by rw [heq]; simp
      have hi1 : γ[l₁.length + 1]? = some y := by rw [heq]; simp
      exact havoid l₁.length x y hi hi1 h.ne

theorem cwc_chain_avoids_edge {V : Type*} (T : SimpleGraph V) (hT : T.IsAcyclic)
    {a b c d : V} (hab : T.Adj a b) (hcd : T.Adj c d) (heq : Sym2.mk a b = Sym2.mk c d)
    (γ : List V) (hchain : γ.IsChain (fun x y => x = y ∨ T.Adj x y))
    (hhead : γ.head? = some b) (hlast : γ.getLast? = some c)
    (havoid : ∀ (i : ℕ) (x y : V), γ[i]? = some x → γ[i + 1]? = some y → x ≠ y →
      Sym2.mk x y ≠ Sym2.mk a b) :
    b = c := by
  rcases Sym2.eq_iff.mp heq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · -- `a = c` and `b = d`: the chain joins the two ends of the edge `s(a,b)` without traversing it,
    -- contradicting the fact that `s(a,b)` is a bridge of the forest `T`.
    exfalso
    have hreach : (T.deleteEdges {Sym2.mk a b}).Reachable b c :=
      reachable_deleteEdges_of_chain T a b γ hchain havoid hhead hlast
    have h2 : (T.deleteEdges {Sym2.mk a b}).Reachable c b :=
      SimpleGraph.reachable_comm.mpr hreach
    rw [← hac] at h2
    have hb : T.IsBridge (Sym2.mk a b) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT) hab
    rw [SimpleGraph.isBridge_iff] at hb
    exact hb h2
  · -- `b = c` already.
    exact hbc

end Work.ORDunwoody.ChordWalk
