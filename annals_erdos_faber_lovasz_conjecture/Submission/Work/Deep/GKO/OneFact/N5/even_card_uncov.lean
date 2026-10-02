import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.even_card_of_matching_closed

/-!
# N5: the uncovered vertices of an inside matching are even in number

Vocabulary: `uncov M` (`Defs.lean`) and `Work.Deep.GKO.IsMatching'`.

* `even_card_of_matching_closed'` — if `N` is a matching and every vertex of a finite set `s` has
  an `N`-neighbour inside `s`, then `s` is a union of `N`-edges and `s.card` is even.  The proof
  builds the subgraph of `N` induced on `s` and applies the parity lemma
  `Work.Deep.GKO.even_card_of_matching_closed` (whose core is `Subgraph.IsMatching.even_card`).

* `even_card_uncov` (the node's statement) — if `A ⊔ B = univ` with `|A| = |B|` and every edge of
  the matching `N` has both ends on the same side, then `#(uncov N)` is even.  Indeed
  `uncov N` is the disjoint union of the `A`-vertices and the `B`-vertices missed by `N`; the
  covered vertices of `A` (resp. of `B`) form an `N`-edge-closed set, hence are even in number,
  so removing them from `A` (resp. `B`) leaves an even number of vertices, and `|A| = |B|` makes
  the total `#(uncov N) = |A ∖ uncov N| + |B ∖ uncov N|` even.
-/

set_option autoImplicit false

namespace Work.Deep.GKO.OneFact.N5

open Classical
open SimpleGraph

noncomputable section

/-- A finite vertex set in which every vertex has an `N`-neighbour inside the set is a union of
`N`-edges, hence has even cardinality: the `N`-mate is a fixed-point-free involution of the set. -/
theorem even_card_of_matching_closed' {n : ℕ} {N : SimpleGraph (Fin n)}
    (hN : Work.Deep.GKO.IsMatching' N) {s : Finset (Fin n)}
    (hcl : ∀ y ∈ s, ∃ z ∈ s, N.Adj y z) : Even s.card := by
  classical
  -- the subgraph of `N` induced on `s`: its `Adj` is `N`-adjacency with both ends in `s`
  refine Work.Deep.GKO.even_card_of_matching_closed
    (R := N) (M := (⊤ : N.Subgraph).induce (↑s)) ?_ ?_
  · intro v hv
    rw [Subgraph.induce_verts] at hv
    obtain ⟨z, hzs, hzv⟩ := hcl v hv
    exact ⟨z, ⟨hv, hzs, hzv⟩, fun w hw => hN v w z hw.2.2 hzv⟩
  · intro y hy
    obtain ⟨z, hzs, hyz⟩ := hcl y hy
    exact ⟨z, hzs, ⟨hy, hzs, hyz⟩⟩

theorem even_card_uncov {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card) (N : SimpleGraph (Fin n))
    (hN : Work.Deep.GKO.IsMatching' N)
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :
    Even (Work.Deep.GKO.OneFact.N5.uncov N).card := by
  classical
  -- the covered and the missed vertices on each side
  set cA : Finset (Fin n) := A.filter (fun v => ∃ w, N.Adj v w) with hcA
  set cB : Finset (Fin n) := B.filter (fun v => ∃ w, N.Adj v w) with hcB
  set uA : Finset (Fin n) := A.filter (fun v => ∀ w, ¬ N.Adj v w) with huA
  set uB : Finset (Fin n) := B.filter (fun v => ∀ w, ¬ N.Adj v w) with huB
  -- each side splits into its covered and its missed vertices
  have hAgood : (A.filter (fun v => ¬ ∃ w, N.Adj v w)) = uA := by
    rw [huA]
    ext v
    simp only [Finset.mem_filter, not_exists]
  have hBgood : (B.filter (fun v => ¬ ∃ w, N.Adj v w)) = uB := by
    rw [huB]
    ext v
    simp only [Finset.mem_filter, not_exists]
  have hAcard : A.card = cA.card + uA.card := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (fun v => ∃ w, N.Adj v w)
    rw [hAgood] at h
    rw [← hcA] at h
    exact h.symm
  have hBcard : B.card = cB.card + uB.card := by
    have h := Finset.card_filter_add_card_filter_not (s := B) (fun v => ∃ w, N.Adj v w)
    rw [hBgood] at h
    rw [← hcB] at h
    exact h.symm
  -- `uncov N` is the disjoint union of `uA` and `uB`
  have hdisj : Disjoint uA uB := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    rw [huA] at hvA
    rw [huB] at hvB
    exact (Finset.disjoint_left.mp hAB (Finset.mem_filter.mp hvA).1)
      (Finset.mem_filter.mp hvB).1
  have huncov : (uncov N).card = uA.card + uB.card := by
    have h1 : (Finset.univ.filter fun v => ∀ w, ¬ N.Adj v w) = uA ∪ uB := by
      rw [← hcov, Finset.filter_union, huA, huB]
    have heq : uncov N = uA ∪ uB := by
      rw [← h1]
      rfl
    rw [heq, Finset.card_union_of_disjoint hdisj]
  -- the covered vertices of each side are even in number
  have hcAeven : Even cA.card := by
    rw [hcA]
    refine even_card_of_matching_closed' hN ?_
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyA, z, hyz⟩ := hy
    have hzA : z ∈ A := by
      rcases hNin y z hyz with h | h
      · exact h.2
      · exact absurd h.1 (Finset.disjoint_left.mp hAB hyA)
    exact ⟨z, by rw [Finset.mem_filter]; exact ⟨hzA, y, (N.adj_comm y z).mp hyz⟩, hyz⟩
  have hcBeven : Even cB.card := by
    rw [hcB]
    refine even_card_of_matching_closed' hN ?_
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyB, z, hyz⟩ := hy
    have hzB : z ∈ B := by
      rcases hNin y z hyz with h | h
      · exact absurd h.1 (Finset.disjoint_right.mp hAB hyB)
      · exact h.2
    exact ⟨z, by rw [Finset.mem_filter]; exact ⟨hzB, y, (N.adj_comm y z).mp hyz⟩, hyz⟩
  -- `|A| = |B|`, and both sides split into an even part and their missed vertices
  rw [huncov]
  have hsum : cA.card + uA.card = cB.card + uB.card := by omega
  have hiff : Even uA.card ↔ Even uB.card := by
    have h : Even (cA.card + uA.card) ↔ Even (cB.card + uB.card) := by rw [hsum]
    rw [Nat.even_add, Nat.even_add] at h
    simpa [hcAeven, hcBeven] using h
  rw [Nat.even_add]
  exact hiff

end

end Work.Deep.GKO.OneFact.N5
