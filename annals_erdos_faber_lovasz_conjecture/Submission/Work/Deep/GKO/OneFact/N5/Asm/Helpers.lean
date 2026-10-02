import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFact.N5.insideNearPerfectClasses
import Submission.Work.Deep.GKO.OneFact.matchingAbsorber
import Submission.Work.Deep.GKO.OneFact.N5.Asm.Params

/-!
# Elementary helpers for the N5 assembly

Bookkeeping lemmas for the cross restriction, for the counting of the "bad" Vizing classes and
for degrees after deleting a union of matchings.  See `Asm.Main` for the assembly itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Classical

namespace Work.Deep.GKO.OneFact.N5.Asm

open Work.Deep.GKO.OneFact

variable {n : ℕ}

/-! ## Elementary bookkeeping for the cross restriction -/

/-- Cross edges between `S ⊆ A` and `T ⊆ B` are the same in `G` and in its cross restriction. -/
lemma crossEdges_crossRestr (G : SimpleGraph (Fin n)) {A B S T : Finset (Fin n)}
    (hSA : S ⊆ A) (hTB : T ⊆ B) :
    Work.Deep.GKO.crossEdges (crossRestr G A B) S T = Work.Deep.GKO.crossEdges G S T := by
  classical
  unfold Work.Deep.GKO.crossEdges
  congr 1
  refine Finset.filter_congr fun p hp => ?_
  rw [Finset.product_eq_sprod, Finset.mem_product] at hp
  exact ⟨fun h => crossRestr_le G A B h, fun h => crossRestr_adj_of (hSA hp.1) (hTB hp.2) h⟩

/-- The neighbours of `v ∈ A` in the cross restriction are its `G`-neighbours in `B`. -/
lemma natCard_neighborSet_crossRestr_mem_left (G : SimpleGraph (Fin n)) {A B : Finset (Fin n)}
    (hAB : Disjoint A B) {v : Fin n} (hv : v ∈ A) :
    Nat.card ((crossRestr G A B).neighborSet v) = Work.Deep.GKO.degIn G v B := by
  classical
  rw [Work.Deep.GKO.degIn_eq_ncard, Nat.card_coe_set_eq]
  congr 1
  ext y
  constructor
  · intro hy
    rw [SimpleGraph.mem_neighborSet] at hy
    rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
    refine ⟨crossRestr_le G A B hy, ?_⟩
    rcases crossRestr_adj_mem hy with ⟨-, hy'⟩ | ⟨hvB, -⟩
    · exact hy'
    · exact absurd hvB (Finset.disjoint_left.mp hAB hv)
  · intro hy
    rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hy
    obtain ⟨h, hyB⟩ := hy
    rw [SimpleGraph.mem_neighborSet]
    exact crossRestr_adj_of hv hyB h

/-- The neighbours of `v ∈ B` in the cross restriction are its `G`-neighbours in `A`. -/
lemma natCard_neighborSet_crossRestr_mem_right (G : SimpleGraph (Fin n)) {A B : Finset (Fin n)}
    (hAB : Disjoint A B) {v : Fin n} (hv : v ∈ B) :
    Nat.card ((crossRestr G A B).neighborSet v) = Work.Deep.GKO.degIn G v A := by
  classical
  rw [Work.Deep.GKO.degIn_eq_ncard, Nat.card_coe_set_eq]
  congr 1
  ext y
  constructor
  · intro hy
    rw [SimpleGraph.mem_neighborSet] at hy
    rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
    refine ⟨crossRestr_le G A B hy, ?_⟩
    rcases crossRestr_adj_mem hy with ⟨hvA, -⟩ | ⟨-, hy'⟩
    · exact False.elim ((Finset.disjoint_left.mp hAB hvA) hv)
    · exact hy'
  · intro hy
    rw [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hy
    obtain ⟨h, hyA⟩ := hy
    rw [SimpleGraph.mem_neighborSet]
    exact (crossRestr_adj_of (a := y) (b := v) hyA hv ((G.adj_comm v y).mp h)).symm

/-- The edges of a graph whose ends both lie on the same side of a bipartition are edge-disjoint
from the edges of a graph whose ends lie on opposite sides. -/
lemma disjoint_of_inside_cross {M K : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (hAB : Disjoint A B)
    (hM : ∀ u v, M.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (hK : ∀ u v, K.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) :
    Disjoint M.edgeSet K.edgeSet := by
  classical
  rw [Set.disjoint_left]
  intro e heM heK
  induction e using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet] at heM heK
    rcases hM u v heM with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      rcases hK u v heK with ⟨huA, hvB⟩ | ⟨huB, hvA⟩
    · exact (Finset.disjoint_left.mp hAB hv) hvB
    · exact (Finset.disjoint_left.mp hAB hu) huB
    · exact (Finset.disjoint_left.mp hAB huA) hu
    · exact (Finset.disjoint_left.mp hAB hvA) hv

/-- A subgraph of a matching is a matching. -/
lemma isMatching'_sdiff {M P : SimpleGraph (Fin n)} (h : Work.Deep.GKO.IsMatching' M) :
    Work.Deep.GKO.IsMatching' (M \ P) := by
  intro v w w' hw hw'
  rw [SimpleGraph.sdiff_adj] at hw hw'
  exact h v w w' hw.1 hw'.1

/-- A subgraph of a matching is a matching. -/
lemma isMatching'_inf {M P : SimpleGraph (Fin n)} (h : Work.Deep.GKO.IsMatching' M) :
    Work.Deep.GKO.IsMatching' (M ⊓ P) := by
  intro v w w' hw hw'
  rw [SimpleGraph.inf_adj] at hw hw'
  exact h v w w' hw.1 hw'.1

/-! ## Counting the bad colour classes -/

/-- If every vertex is uncovered by at most `m` of the members of a family of matchings, then the
number of members covering at most `s` vertices is bounded by `n · m / (s + 1)`. -/
lemma bad_count_le {c₀ : ℕ} (N : Fin c₀ → SimpleGraph (Fin n)) {s m : ℕ}
    (hNuncov : ∀ v : Fin n, (Finset.univ.filter fun j => v ∈ uncov (N j)).card ≤ m) :
    (Finset.univ.filter fun j : Fin c₀ => ¬ ((uncov (N j)).card ≤ s)).card * (s + 1)
      ≤ n * m := by
  classical
  have key : ∀ j : Fin c₀, (uncov (N j)).card
      = ∑ v : Fin n, (if v ∈ uncov (N j) then 1 else 0) := by
    intro j
    have h : uncov (N j) = Finset.univ.filter (fun v : Fin n => v ∈ uncov (N j)) := by
      ext v; simp
    rw [h, Finset.card_filter]
    simp
  have hsum : ∑ j : Fin c₀, (uncov (N j)).card
      = ∑ v : Fin n, (Finset.univ.filter fun j : Fin c₀ => v ∈ uncov (N j)).card := by
    simp only [key]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter]
  have hmain : (Finset.univ.filter fun j : Fin c₀ => ¬ ((uncov (N j)).card ≤ s)).card * (s + 1)
      ≤ ∑ j : Fin c₀, (uncov (N j)).card := by
    calc (Finset.univ.filter fun j : Fin c₀ => ¬ ((uncov (N j)).card ≤ s)).card * (s + 1)
        = ∑ _j ∈ (Finset.univ.filter fun j : Fin c₀ => ¬ ((uncov (N j)).card ≤ s)), (s + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ j ∈ (Finset.univ.filter fun j : Fin c₀ => ¬ ((uncov (N j)).card ≤ s)),
            (uncov (N j)).card := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          omega
      _ ≤ ∑ j : Fin c₀, (uncov (N j)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
  rw [hsum] at hmain
  calc (Finset.univ.filter fun j : Fin c₀ => ¬ ((uncov (N j)).card ≤ s)).card * (s + 1)
      ≤ ∑ v : Fin n, (Finset.univ.filter fun j : Fin c₀ => v ∈ uncov (N j)).card := hmain
    _ ≤ ∑ _v : Fin n, m := Finset.sum_le_sum fun v _ => hNuncov v
    _ = n * m := by simp

/-! ## Degrees after deleting a union of matchings -/

/-- Deleting a graph from `K` costs at each vertex at most the number of common neighbours of `K`
and the deleted graph: `deg_K u T ≤ deg_{K \ G'} u T + |N_K(u) ∩ N_{G'}(u)|`. -/
lemma degIn_le_degIn_sdiff_add (K G' : SimpleGraph (Fin n)) (u : Fin n) (T : Finset (Fin n)) :
    Work.Deep.GKO.degIn K u T ≤ Work.Deep.GKO.degIn (K \ G') u T
      + Nat.card ((K.neighborSet u ∩ G'.neighborSet u : Set (Fin n))) := by
  classical
  rw [Work.Deep.GKO.degIn_eq_ncard, Work.Deep.GKO.degIn_eq_ncard, Nat.card_coe_set_eq]
  have hsub : K.neighborSet u ∩ (T : Set (Fin n)) ⊆
      ((K \ G').neighborSet u ∩ (T : Set (Fin n))) ∪ (K.neighborSet u ∩ G'.neighborSet u) := by
    intro z hz
    rw [Set.mem_inter_iff] at hz
    have hKz : K.Adj u z := (SimpleGraph.mem_neighborSet K u z).mp hz.1
    by_cases h : (K \ G').Adj u z
    · exact Or.inl ⟨(SimpleGraph.mem_neighborSet _ u z).mpr h, hz.2⟩
    · refine Or.inr ⟨hz.1, ?_⟩
      by_contra hg
      rw [SimpleGraph.sdiff_adj] at h
      exact h ⟨hKz, hg⟩
  refine le_trans (Set.ncard_le_ncard hsub) ?_
  exact Set.ncard_union_le _ _

/-- A perfect matching is a matching. -/
lemma isMatching'_of_isPerfectMatching {G P : SimpleGraph (Fin n)}
    (h : Work.Deep.GKO.IsPerfectMatching' G P) : Work.Deep.GKO.IsMatching' P := by
  intro v w w' hw hw'
  obtain ⟨u, -, huniq⟩ := h.2 v
  rw [huniq w hw, huniq w' hw']

/-- The number of indices satisfying a predicate is at most the cardinality of the corresponding
filter of the universal finset. -/
lemma ncard_setOf_le_of_filter {c : ℕ} (p : Fin c → Prop) {m : ℕ}
    (h : (Finset.univ.filter p).card ≤ m) : ({i | p i} : Set (Fin c)).ncard ≤ m := by
  classical
  have h1 : ({i | p i} : Set (Fin c)).ncard = (Finset.univ.filter p).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp
  omega

end Work.Deep.GKO.OneFact.N5.Asm
