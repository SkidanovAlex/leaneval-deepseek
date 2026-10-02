import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

namespace Work.Deep.GKO.Abs

/-- **The combinatorial core of `splitAlong`.**  A finite set splits into pairwise disjoint
subsets of prescribed sizes, as soon as the prescribed sizes sum to the cardinality of the
set.  (The covering condition is a consequence of the cardinality count and is obtained for
free from the induction.) -/
lemma exists_disjoint_partition {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset β) (t : Finset α) (g : α → ℕ) (h : ∑ a ∈ t, g a = s.card) :
    ∃ S : α → Finset β,
      (∀ a ∈ t, S a ⊆ s) ∧
      (∀ a ∈ t, (S a).card = g a) ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → Disjoint (S a) (S b)) ∧
      s ⊆ t.biUnion S := by
  classical
  induction t using Finset.induction_on generalizing s with
  | empty =>
      have hs : s = ∅ := Finset.card_eq_zero.mp (by simpa using h.symm)
      subst hs
      exact ⟨fun _ => ∅, by simp, by simp, by simp, by simp⟩
  | insert a t' ha ih =>
      have hsum : g a + ∑ b ∈ t', g b = s.card := by
        rw [← h, Finset.sum_insert ha]
      have hle : g a ≤ s.card := by omega
      obtain ⟨A, hAs, hAcard⟩ := Finset.exists_subset_card_eq hle
      have hcard' : ∑ b ∈ t', g b = (s \ A).card := by
        rw [Finset.card_sdiff_of_subset hAs, hAcard]
        omega
      obtain ⟨S', hS'1, hS'2, hS'3, hS'4⟩ := ih (s \ A) hcard'
      have hne : ∀ b ∈ t', b ≠ a := fun b hb hba => ha (by rw [← hba]; exact hb)
      refine ⟨Function.update S' a A, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb'
        · rw [Function.update_self]; exact hAs
        · rw [Function.update_of_ne (hne b hb')]
          exact fun x hx => (Finset.mem_sdiff.mp (hS'1 b hb' hx)).1
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb'
        · rw [Function.update_self, hAcard]
        · rw [Function.update_of_ne (hne b hb'), hS'2 b hb']
      · intro b hb c hc hbc
        rcases Finset.mem_insert.mp hb with rfl | hb' <;>
          rcases Finset.mem_insert.mp hc with rfl | hc'
        · exact absurd rfl hbc
        · rw [Function.update_self, Function.update_of_ne (hne c hc')]
          exact Finset.disjoint_left.mpr fun x hxA hxS =>
            (Finset.mem_sdiff.mp (hS'1 c hc' hxS)).2 hxA
        · rw [Function.update_of_ne (hne b hb'), Function.update_self]
          exact Finset.disjoint_left.mpr fun x hxS hxA =>
            (Finset.mem_sdiff.mp (hS'1 b hb' hxS)).2 hxA
        · rw [Function.update_of_ne (hne b hb'), Function.update_of_ne (hne c hc')]
          exact hS'3 b hb' c hc' hbc
      · intro x hx
        by_cases hxA : x ∈ A
        · exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self a t', by
            rw [Function.update_self]; exact hxA⟩
        · obtain ⟨b, hb', hxb⟩ :=
            Finset.mem_biUnion.mp (hS'4 (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))
          refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_insert_of_mem hb', ?_⟩
          rw [Function.update_of_ne (hne b hb')]
          exact hxb

theorem splitAlong {n a : ℕ} (PA : Fin a → SimpleGraph (Fin n))
    (hM : ∀ i, Work.Deep.GKO.IsMatching' (PA i))
    (hdisj : ∀ i j : Fin a, i ≠ j → Disjoint (PA i).edgeSet (PA j).edgeSet)
    {ι : Type*} [Fintype ι] (f : ι → Fin a) (ν : ι → ℕ)
    (hfib : ∀ i, ∑ k ∈ (Finset.univ.filter (fun k : ι => f k = i)), ν k
        = Nat.card (PA i).edgeSet) :
    ∃ Q : ι → SimpleGraph (Fin n),
      (∀ k, Work.Deep.GKO.IsMatching' (Q k)) ∧
      (∀ k, Q k ≤ PA (f k)) ∧
      (∀ k, Nat.card (Q k).edgeSet = ν k) ∧
      (∀ k l : ι, k ≠ l → Disjoint (Q k).edgeSet (Q l).edgeSet) ∧
      (∀ e : Sym2 (Fin n), (∃ i, e ∈ (PA i).edgeSet) → ∃ k, e ∈ (Q k).edgeSet) := by
  classical
  -- The class of `i : Fin a` is the set of indices `k` with `f k = i`.
  let F : Fin a → Finset ι := fun i => Finset.univ.filter (fun k : ι => f k = i)
  -- `Nat.card` of the edge set is the number of edges, as a `Finset`.
  have hcard : ∀ i : Fin a, (PA i).edgeFinset.card = Nat.card (PA i).edgeSet := by
    intro i
    rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  -- Split the edges of each `PA i` into pieces indexed by the class of `i`, with sizes `ν`.
  have hex : ∀ i : Fin a, ∃ S : ι → Finset (Sym2 (Fin n)),
      (∀ k ∈ F i, S k ⊆ (PA i).edgeFinset) ∧
      (∀ k ∈ F i, (S k).card = ν k) ∧
      (∀ k ∈ F i, ∀ l ∈ F i, k ≠ l → Disjoint (S k) (S l)) ∧
      (PA i).edgeFinset ⊆ (F i).biUnion S := by
    intro i
    exact exists_disjoint_partition (PA i).edgeFinset (F i) ν
      (by rw [hcard i]; exact hfib i)
  let S : Fin a → ι → Finset (Sym2 (Fin n)) := fun i => Classical.choose (hex i)
  have hS : ∀ i : Fin a,
      (∀ k ∈ F i, S i k ⊆ (PA i).edgeFinset) ∧
      (∀ k ∈ F i, (S i k).card = ν k) ∧
      (∀ k ∈ F i, ∀ l ∈ F i, k ≠ l → Disjoint (S i k) (S i l)) ∧
      (PA i).edgeFinset ⊆ (F i).biUnion (S i) := fun i => Classical.choose_spec (hex i)
  -- The piece assigned to `k` is the piece of the class of `f k`.
  let T : ι → Finset (Sym2 (Fin n)) := fun k => S (f k) k
  have hTsub : ∀ k : ι, (T k : Set (Sym2 (Fin n))) ⊆ (PA (f k)).edgeSet := by
    intro k e he
    have hk : k ∈ F (f k) := Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩
    exact (SimpleGraph.mem_edgeFinset).mp ((hS (f k)).1 k hk he)
  -- A set of genuine edges gives back exactly that set when made into a graph.
  have hedge : ∀ k : ι, (SimpleGraph.fromEdgeSet (T k : Set (Sym2 (Fin n)))).edgeSet
      = (T k : Set (Sym2 (Fin n))) := by
    intro k
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine Set.eq_of_subset_of_subset Set.sdiff_subset fun z hz => ⟨hz, ?_⟩
    rw [Sym2.mem_diagSet]
    exact SimpleGraph.not_isDiag_of_mem_edgeSet (G := PA (f k)) (hTsub k hz)
  have hle : ∀ k : ι, SimpleGraph.fromEdgeSet (T k : Set (Sym2 (Fin n))) ≤ PA (f k) := fun k =>
    (SimpleGraph.fromEdgeSet_le (PA (f k))).mpr (Set.Subset.trans Set.sdiff_subset (hTsub k))
  refine ⟨fun k => SimpleGraph.fromEdgeSet (T k : Set (Sym2 (Fin n))), ?_, ?_, ?_, ?_, ?_⟩
  · -- each piece is a matching, being a subgraph of the matching `PA (f k)`
    intro k u v w huv huw
    exact hM (f k) u v w (hle k huv) (hle k huw)
  · intro k
    exact hle k
  · -- the prescribed sizes
    intro k
    rw [hedge k]
    have h3 : Nat.card (T k : Set (Sym2 (Fin n))) = (T k).card := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [h3]
    exact (hS (f k)).2.1 k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩)
  · -- pieces of the same class are disjoint by construction, of different classes by
    -- edge-disjointness of the `PA i`
    intro k l hkl
    rw [hedge k, hedge l]
    by_cases hfl : f k = f l
    · have hk : k ∈ F (f k) := Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩
      have hl : l ∈ F (f k) := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hfl.symm⟩
      have hdisj' := (hS (f k)).2.2.1 k hk l hl hkl
      have h2 : T l = S (f k) l := by
        show S (f l) l = S (f k) l
        rw [← hfl]
      rw [show T k = S (f k) k from rfl, h2]
      exact Finset.disjoint_coe.mpr hdisj'
    · refine Set.disjoint_left.mpr fun e hek hel => ?_
      exact Set.disjoint_left.mp (hdisj (f k) (f l) hfl) (hTsub k hek) (hTsub l hel)
  · -- covering: every edge of some `PA i` is a piece of the class of `i`
    intro e he
    obtain ⟨i, hi⟩ := he
    have hi' : e ∈ (PA i).edgeFinset := (SimpleGraph.mem_edgeFinset).mpr hi
    obtain ⟨k, hkF, hkT⟩ := Finset.mem_biUnion.mp ((hS i).2.2.2 hi')
    have hfk : f k = i := (Finset.mem_filter.mp hkF).2
    refine ⟨k, ?_⟩
    rw [hedge k]
    show e ∈ S (f k) k
    rw [show f k = i from hfk]
    exact hkT

end Work.Deep.GKO.Abs
