import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# A linear forest is the union of two matchings

A linear forest -- an acyclic graph of maximum degree at most two -- is a disjoint union of
paths.  Colouring the edges of every path alternately partitions its edge set into two
matchings, i.e. gives a proper edge colouring with two colours.

This is used in the reduction for the two colours spent on each of the spanning linear forests
`F_i` that are removed to make the graph regular.

The proof is the classical peeling induction on the number of edges.  A nonempty finite forest
has a leaf `v` (take a longest path; its endpoint cannot have a neighbour outside the path, and
two neighbours on the path would close a cycle), with unique neighbour `u`.  Removing the edge
`uv` leaves a linear forest, so by induction it has a two-colouring; the edge `uv` gets the
colour which is missing at `u` (the vertex `v` is isolated after the deletion, and `u` has lost
one of its at most two edges).

## Implementation notes

* The two-colouring property is phrased directly in terms of `Sym2 (Fin n)` (the type of
  unordered pairs) to avoid `simpleGraph`/`edgeSet` glue, and a two-colouring is converted into
  a matching decomposition at the very end (`hasMatchingDecomposition_of_edgeColoring`).
* We never use `SimpleGraph.degree`/`neighborFinset`, only `Set.ncard` of `neighborSet`/`edgeSet`,
  because in this version of Mathlib the `Fintype` instance for the neighbour set of a vertex is
  not synthesized automatically.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO

open SimpleGraph

variable {n : ℕ}

/-! ## Auxiliary lemmas -/

/-- Every element of the edge set of a graph is a pair of adjacent vertices. -/
lemma exists_adj_of_mem_edgeSet {F : SimpleGraph (Fin n)} {e : Sym2 (Fin n)}
    (he : e ∈ F.edgeSet) : ∃ u v : Fin n, e = s(u, v) ∧ F.Adj u v := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, rfl, (SimpleGraph.mem_edgeSet (G := F) (v := a) (w := b)).mp he⟩

/-- If `v` is a leaf of `F` with unique neighbour `u`, every edge of `F` at `v` is `s(u,v)`. -/
lemma eq_sym2_of_mem_edgeSet_of_mem {F : SimpleGraph (Fin n)} {u v : Fin n}
    (hv : F.neighborSet v = {u}) {f : Sym2 (Fin n)} (hf : f ∈ F.edgeSet) (hvf : v ∈ f) :
    f = s(u, v) := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hvf
  rw [SimpleGraph.mem_edgeSet] at hf
  have hw : w ∈ F.neighborSet v := hf
  rw [hv, Set.mem_singleton_iff] at hw
  rw [hw, Sym2.eq_swap]

/-- Membership in the edge set of `F.deleteEdges {e₀}`. -/
lemma mem_edgeSet_deleteEdges_singleton_iff {F : SimpleGraph (Fin n)} {e₀ e : Sym2 (Fin n)} :
    e ∈ (F.deleteEdges {e₀}).edgeSet ↔ e ∈ F.edgeSet ∧ e ≠ e₀ := by
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]

/-- **A nonempty finite acyclic graph has a leaf.**  Take a longest path; its endpoint `v` cannot
have a neighbour outside the path (the path would extend) nor two neighbours on the path (that
would give a cycle), so `v` has exactly one neighbour. -/
lemma exists_leaf_of_acyclic {F : SimpleGraph (Fin n)} (hac : F.IsAcyclic)
    (he : (F.edgeSet).Nonempty) :
    ∃ u v : Fin n, F.Adj u v ∧ F.neighborSet v = {u} := by
  obtain ⟨e, hee⟩ := he
  obtain ⟨a₀, b₀, -, hab₀⟩ := exists_adj_of_mem_edgeSet hee
  haveI : Nonempty (Fin n) := ⟨a₀⟩
  obtain ⟨a, b, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length F
  have hnil : ¬ p.Nil := by
    intro h
    have hpath : (SimpleGraph.Walk.cons hab₀ SimpleGraph.Walk.nil).IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [hab₀.ne]
    have hle := hmax a₀ b₀ _ hpath
    rw [SimpleGraph.Walk.length_eq_zero_iff.mpr h] at hle
    simp at hle
  refine ⟨p.penultimate, b, p.adj_penultimate hnil, ?_⟩
  ext w
  constructor
  · intro hw
    rw [Set.mem_singleton_iff]
    by_cases hws : w ∈ p.support
    · exact hac.eq_penultimate_of_adj_end hp hw hws
    · exfalso
      have hle := hmax a w (p.concat hw) (hp.concat hws hw)
      have hlen : (p.concat hw).length = p.length + 1 :=
        SimpleGraph.Walk.length_concat p hw
      omega
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (p.adj_penultimate hnil).symm

/-- After deleting the edge `uv` from a graph in which `u` has at most two neighbours, `u` has at
most one neighbour left. -/
lemma neighborSet_deleteEdge_ncard_le_one {F : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : F.Adj u v) (hdeg : (F.neighborSet u).ncard ≤ 2) :
    ((F.deleteEdges {s(u, v)}).neighborSet u).ncard ≤ 1 := by
  have hsub : (F.deleteEdges {s(u, v)}).neighborSet u ⊆ F.neighborSet u := by
    intro z hz
    exact (SimpleGraph.deleteEdges_adj.mp hz).1
  have hv : v ∈ F.neighborSet u := huv
  have hv' : v ∉ (F.deleteEdges {s(u, v)}).neighborSet u := by
    intro h
    exact (SimpleGraph.deleteEdges_adj.mp h).2 (by simp)
  have hss : (F.deleteEdges {s(u, v)}).neighborSet u ⊂ F.neighborSet u :=
    ⟨hsub, fun hsub' => hv' (hsub' hv)⟩
  have := Set.ncard_lt_ncard hss
  omega

/-- If a vertex has at most one neighbour, there is at most one edge at it. -/
lemma edge_at_vertex_unique {F : SimpleGraph (Fin n)} {u : Fin n}
    (h1 : (F.neighborSet u).ncard ≤ 1) {f g : Sym2 (Fin n)}
    (hf : f ∈ F.edgeSet) (huf : u ∈ f) (hg : g ∈ F.edgeSet) (hug : u ∈ g) : f = g := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp huf
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hug
  have hw : w ∈ F.neighborSet u := (SimpleGraph.mem_edgeSet (G := F) (v := u) (w := w)).mp hf
  have hz : z ∈ F.neighborSet u := (SimpleGraph.mem_edgeSet (G := F) (v := u) (w := z)).mp hg
  have hiff : (F.neighborSet u).ncard ≤ 1 ↔
      ∀ a ∈ F.neighborSet u, ∀ b ∈ F.neighborSet u, a = b :=
    Set.ncard_le_one (Set.toFinite _)
  rw [hiff.mp h1 w hw z hz]

/-! ## A two-colouring of a linear forest -/

/-- Every linear forest on `Fin n` whose edge set has `m` elements admits a proper edge colouring
with two colours, i.e. a colouring in which two distinct edges sharing a vertex get different
colours. -/
theorem exists_two_coloring_of_linearForest : ∀ (m : ℕ) (F : SimpleGraph (Fin n)),
    IsLinearForest F → (F.edgeSet).ncard = m →
      ∃ c : Sym2 (Fin n) → Fin 2,
        ∀ e ∈ F.edgeSet, ∀ e' ∈ F.edgeSet, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → c e ≠ c e' := by
  intro m
  induction m with
  | zero =>
      intro F hF hcard
      refine ⟨fun _ => 0, ?_⟩
      intro e he
      exfalso
      rw [Set.ncard_eq_zero] at hcard
      rw [hcard] at he
      exact he
  | succ m ih =>
      intro F hF hcard
      classical
      have hne : (F.edgeSet).Nonempty := by
        rw [← Set.ncard_pos]
        omega
      obtain ⟨u, v, huv, hv⟩ := exists_leaf_of_acyclic hF.1 hne
      have he₀ : s(u, v) ∈ F.edgeSet :=
        (SimpleGraph.mem_edgeSet (G := F) (v := u) (w := v)).mpr huv
      have hlin' : IsLinearForest (F.deleteEdges {s(u, v)}) := by
        refine ⟨SimpleGraph.IsAcyclic.anti (SimpleGraph.deleteEdges_le _) hF.1, ?_⟩
        intro x
        exact le_trans
          (Set.ncard_le_ncard fun z hz => (SimpleGraph.deleteEdges_adj.mp hz).1) (hF.2 x)
      have hcard' : ((F.deleteEdges {s(u, v)}).edgeSet).ncard = m := by
        rw [SimpleGraph.edgeSet_deleteEdges, Set.ncard_sdiff_singleton_of_mem he₀]
        omega
      obtain ⟨c', hc'⟩ := ih (F.deleteEdges {s(u, v)}) hlin' hcard'
      have hdeg_u : ((F.deleteEdges {s(u, v)}).neighborSet u).ncard ≤ 1 :=
        neighborSet_deleteEdge_ncard_le_one huv (hF.2 u)
      -- the colour of the peeled edge is the colour missing at `u`
      let i : Fin 2 :=
        if ∃ f ∈ (F.deleteEdges {s(u, v)}).edgeSet, u ∈ f ∧ c' f = 0 then 1 else 0
      have hi1 : (∃ f ∈ (F.deleteEdges {s(u, v)}).edgeSet, u ∈ f ∧ c' f = 0) → i = 1 := by
        intro h; dsimp only [i]; rw [if_pos h]
      have hi0 : ¬ (∃ f ∈ (F.deleteEdges {s(u, v)}).edgeSet, u ∈ f ∧ c' f = 0) → i = 0 := by
        intro h; dsimp only [i]; rw [if_neg h]
      -- an edge of `F.deleteEdges {s(u,v)}` through `u` receives the colour `i`
      have hcolour_at_u : ∀ g : Sym2 (Fin n),
          g ∈ (F.deleteEdges {s(u, v)}).edgeSet → u ∈ g → i ≠ c' g := by
        intro g hg hug
        by_cases hc0 : c' g = 0
        · rw [hi1 ⟨g, hg, hug, hc0⟩, hc0]
          decide
        · rw [hi0 (fun ⟨f, hf, huf, hc0f⟩ => by
            have hfg : f = g := edge_at_vertex_unique hdeg_u hf huf hg hug
            rw [hfg] at hc0f
            exact hc0 hc0f)]
          exact fun h => hc0 h.symm
      refine ⟨fun e => if e = s(u, v) then i else c' e, ?_⟩
      intro e he e' he' hne' ⟨p, hpe, hpe'⟩
      change (if e = s(u, v) then i else c' e) ≠ (if e' = s(u, v) then i else c' e')
      rcases eq_or_ne e (s(u, v)) with h1 | h1
      · -- `e` is the peeled edge; the shared vertex is `u` or `v`
        rw [if_pos h1]
        have hp : p = u ∨ p = v := by
          have hp' : p ∈ s(u, v) := h1 ▸ hpe
          rw [Sym2.mem_iff] at hp'
          exact hp'
        rcases hp with hp | hp
        · have hue' : u ∈ e' := hp ▸ hpe'
          have h2 : e' ≠ s(u, v) := fun h => hne' (h1.trans h.symm)
          have he'F' : e' ∈ (F.deleteEdges {s(u, v)}).edgeSet :=
            mem_edgeSet_deleteEdges_singleton_iff.mpr ⟨he', h2⟩
          rw [if_neg h2]
          exact hcolour_at_u e' he'F' hue'
        · have hve' : v ∈ e' := hp ▸ hpe'
          exact absurd (h1.trans (eq_sym2_of_mem_edgeSet_of_mem hv he' hve').symm) hne'
      · rcases eq_or_ne e' (s(u, v)) with h2 | h2
        · -- `e'` is the peeled edge; the shared vertex is `u` or `v`
          rw [if_neg h1, if_pos h2]
          have hp : p = u ∨ p = v := by
            have hp' : p ∈ s(u, v) := h2 ▸ hpe'
            rw [Sym2.mem_iff] at hp'
            exact hp'
          rcases hp with hp | hp
          · have hue : u ∈ e := hp ▸ hpe
            have heF' : e ∈ (F.deleteEdges {s(u, v)}).edgeSet :=
              mem_edgeSet_deleteEdges_singleton_iff.mpr ⟨he, h1⟩
            exact (hcolour_at_u e heF' hue).symm
          · have hve : v ∈ e := hp ▸ hpe
            exact absurd ((eq_sym2_of_mem_edgeSet_of_mem hv he hve).trans h2.symm) hne'
        · -- neither edge is peeled: use the colouring of `F.deleteEdges {s(u,v)}`
          rw [if_neg h1, if_neg h2]
          exact hc' e (mem_edgeSet_deleteEdges_singleton_iff.mpr ⟨he, h1⟩)
            e' (mem_edgeSet_deleteEdges_singleton_iff.mpr ⟨he', h2⟩) hne' ⟨p, hpe, hpe'⟩

/-! ## From a two-colouring to a matching decomposition -/

/-- A proper edge colouring with `k` colours yields a decomposition of the edge set into `k`
matchings: the matching of colour `i` consists of the edges of colour `i`. -/
theorem hasMatchingDecomposition_of_edgeColoring {F : SimpleGraph (Fin n)} {k : ℕ}
    {c : Sym2 (Fin n) → Fin k}
    (hc : ∀ e ∈ F.edgeSet, ∀ e' ∈ F.edgeSet, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → c e ≠ c e') :
    HasMatchingDecomposition F k := by
  refine ⟨fun i => F.deleteEdges {e | c e ≠ i}, ?_, ?_, ?_, ?_⟩
  · -- each colour class is a matching
    intro i x y y' hxy hxy'
    rw [SimpleGraph.deleteEdges_adj] at hxy hxy'
    by_contra hne
    have heq : s(x, y) ≠ s(x, y') := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hne h2
      · exact hxy.1.ne' h2
    have h1 : c (s(x, y)) = i := not_not.mp hxy.2
    have h2 : c (s(x, y')) = i := not_not.mp hxy'.2
    exact absurd (hc (s(x, y)) ((SimpleGraph.mem_edgeSet (G := F) (v := x) (w := y)).mpr hxy.1)
      (s(x, y')) ((SimpleGraph.mem_edgeSet (G := F) (v := x) (w := y')).mpr hxy'.1) heq
      ⟨x, by simp, by simp⟩) (by simp [h1, h2])
  · intro i
    exact SimpleGraph.deleteEdges_le _
  · -- the colour classes are pairwise edge disjoint
    intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff] at hei hej
    have h1 : c e = i := not_not.mp hei.2
    have h2 : c e = j := not_not.mp hej.2
    exact hij (h1.symm.trans h2)
  · -- every edge of `F` has a colour
    intro e he
    exact ⟨c e, by
      rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff]
      exact ⟨he, by simp⟩⟩

/-- A linear forest (acyclic, maximum degree at most two) has its edge set partitioned into two matchings: colour the edges of each component path alternately.  Used in the reduction for the two colours spent on each of the spanning linear forests `F_i` that are removed to make the graph regular. -/
theorem linearForest_matchingDecomposition {n : ℕ} (F : SimpleGraph (Fin n))
    (hF : Work.Deep.GKO.IsLinearForest F) : Work.Deep.GKO.HasMatchingDecomposition F 2 := by
  obtain ⟨c, hc⟩ := exists_two_coloring_of_linearForest (F.edgeSet).ncard F hF rfl
  exact hasMatchingDecomposition_of_edgeColoring hc

end Work.Deep.GKO
