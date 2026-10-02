import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

namespace Work.Deep.GKO

/-! ## Splitting a matching into matchings of bounded size

Fix an enumeration `f : Fin m ↪ Sym2 (Fin n)` of the `m` edges of a matching `M`.  For
`s > 0` and `i : Fin (1 + m / s)` let `matchBlock s f i` be the set of edges whose index
`j` satisfies `j / s = i`; these are exactly the indices in the interval `[i*s, (i+1)*s)`,
so each block has at most `s` elements, distinct blocks are disjoint, and every index `j`
belongs to block `j / s < 1 + m / s`.  Converting each block into the graph
`fromEdgeSet` of the corresponding edge set produces the required decomposition of `M`.
-/

/-- The `i`-th block of an enumeration `f` of the edges of a graph: the edges whose index
`j` satisfies `j / s = i`, i.e. the edges with index in `[i*s, (i+1)*s)`. -/
private def matchBlock {n m k : ℕ} (s : ℕ) (f : Fin m ↪ Sym2 (Fin n)) (i : Fin k) :
    Finset (Sym2 (Fin n)) :=
  (Finset.univ.filter (fun j : Fin m => j.val / s = i.val)).map f

private lemma mem_matchBlock {n m k : ℕ} {s : ℕ} {f : Fin m ↪ Sym2 (Fin n)} {i : Fin k}
    {x : Sym2 (Fin n)} :
    x ∈ matchBlock s f i ↔ ∃ j : Fin m, j.val / s = i.val ∧ f j = x := by
  simp [matchBlock, Finset.mem_map]

/-- Each block of an enumeration into blocks of consecutive indices has at most `s` edges. -/
private lemma matchBlock_card_le {n m k : ℕ} {s : ℕ} (hs : 0 < s)
    (f : Fin m ↪ Sym2 (Fin n)) (i : Fin k) : (matchBlock s f i).card ≤ s := by
  rw [matchBlock, Finset.card_map]
  calc (Finset.univ.filter (fun j : Fin m => j.val / s = i.val)).card
      = ((Finset.univ.filter (fun j : Fin m => j.val / s = i.val)).map
          ⟨Fin.val, Fin.val_injective⟩).card := by rw [Finset.card_map]
    _ ≤ (Finset.Ico (i.val * s) ((i.val + 1) * s)).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_map] at hj
        obtain ⟨j', hj', rfl⟩ := hj
        rw [Finset.mem_filter] at hj'
        rw [Finset.mem_Ico]
        obtain ⟨-, hj'⟩ := hj'
        exact ⟨by have := Nat.div_mul_le_self j'.val s; rwa [hj'] at this,
               by have := Nat.lt_mul_div_succ j'.val hs
                  rw [hj'] at this
                  rwa [Nat.mul_comm] at this⟩
    _ = s := by
        rw [Nat.card_Ico]
        have h : (i.val + 1) * s = i.val * s + s := by ring
        omega

/-- Distinct blocks of an enumeration are disjoint (an index determines its block). -/
private lemma disjoint_matchBlock {n m k : ℕ} {s : ℕ} (f : Fin m ↪ Sym2 (Fin n))
    {i j : Fin k} (hij : i ≠ j) : Disjoint (matchBlock s f i) (matchBlock s f j) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_matchBlock] at hx hx'
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hba⟩ := hx'
  have hab : a = b := f.injective hba.symm
  refine hij (Fin.ext ?_)
  rw [← ha, ← hb, hab]

/-- For a set `T` of edges of `M`, the edge set of `fromEdgeSet T` is `T` (all the edges
involved are genuine two-element edges). -/
private lemma edgeSet_fromEdgeSet_of_subset {n : ℕ} {M : SimpleGraph (Fin n)}
    {T : Set (Sym2 (Fin n))} (hT : T ⊆ M.edgeSet) :
    (SimpleGraph.fromEdgeSet T).edgeSet = T := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact Set.eq_of_subset_of_subset Set.sdiff_subset fun z hz =>
    ⟨hz, by
      rw [Sym2.mem_diagSet]
      exact SimpleGraph.not_isDiag_of_mem_edgeSet (G := M) (hT hz)⟩

/-- A matching can be split into matchings of bounded size: for every `s > 0` the edge set of a matching `M` partitions into at most `1 + |E(M)| / s` matchings, each with at most `s` edges.  Used to make each set of leaves of the removed spanning linear forests small enough for the spanning-linkage lemma. -/
theorem exists_matchingSplit {n : ℕ} (M : SimpleGraph (Fin n)) (hM : Work.Deep.GKO.IsMatching' M)
    {s : ℕ} (hs : 0 < s) :
    ∃ (k : ℕ) (M' : Fin k → SimpleGraph (Fin n)),
      (∀ i, Work.Deep.GKO.IsMatching' (M' i)) ∧ (∀ i, M' i ≤ M) ∧
      (∀ i, Nat.card ((M' i).edgeSet) ≤ s) ∧
      (∀ i j, i ≠ j → Disjoint (M' i).edgeSet (M' j).edgeSet) ∧
      (∀ e ∈ M.edgeSet, ∃ i, e ∈ (M' i).edgeSet) ∧ k ≤ 1 + Nat.card M.edgeSet / s := by
  classical
  -- write `m` for the number of edges of `M`
  set m : ℕ := Nat.card M.edgeSet with hm
  have henumeq : Fintype.card ↥M.edgeSet = m := by rw [hm, Nat.card_eq_fintype_card]
  -- enumerate the edges of `M` as `e 0, …, e (m-1)`
  obtain ⟨e, he_bij⟩ : ∃ e : Fin m → ↥M.edgeSet, Function.Bijective e :=
    ⟨(finCongr henumeq).symm.trans (Fintype.equivFin ↥M.edgeSet).symm, Equiv.bijective _⟩
  let emb : Fin m ↪ Sym2 (Fin n) :=
    ⟨fun j => (e j : Sym2 (Fin n)), fun _ _ h => he_bij.1 (Subtype.coe_injective h)⟩
  -- every block consists of edges of `M`
  have hS_sub : ∀ i : Fin (1 + m / s),
      (↑(matchBlock s emb i) : Set (Sym2 (Fin n))) ⊆ M.edgeSet := by
    intro i x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨j, -, hjx⟩ := mem_matchBlock.mp hx
    rw [← hjx]
    exact (e j).2
  have hM'le : ∀ i : Fin (1 + m / s),
      SimpleGraph.fromEdgeSet (↑(matchBlock s emb i) : Set (Sym2 (Fin n))) ≤ M :=
    fun i => (SimpleGraph.fromEdgeSet_le M).mpr (Set.Subset.trans Set.sdiff_subset (hS_sub i))
  have hcard : ∀ i : Fin (1 + m / s),
      Nat.card ((SimpleGraph.fromEdgeSet (↑(matchBlock s emb i) :
        Set (Sym2 (Fin n)))).edgeSet) ≤ s :=
    fun i => by
      rw [edgeSet_fromEdgeSet_of_subset (hS_sub i)]
      simpa using matchBlock_card_le hs emb i
  have hdisj : ∀ i j : Fin (1 + m / s), i ≠ j →
      Disjoint ((SimpleGraph.fromEdgeSet (↑(matchBlock s emb i) : Set (Sym2 (Fin n)))).edgeSet)
        ((SimpleGraph.fromEdgeSet (↑(matchBlock s emb j) : Set (Sym2 (Fin n)))).edgeSet) :=
    fun i j hij => by
      rw [edgeSet_fromEdgeSet_of_subset (hS_sub i), edgeSet_fromEdgeSet_of_subset (hS_sub j)]
      exact Finset.disjoint_coe.mpr (disjoint_matchBlock emb hij)
  refine ⟨1 + m / s,
    fun i => SimpleGraph.fromEdgeSet (↑(matchBlock s emb i) : Set (Sym2 (Fin n))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- each part is a matching, being a subgraph of `M`
    intro i v w w' hvw hvw'
    exact hM v w w' (hM'le i hvw) (hM'le i hvw')
  · exact hM'le
  · exact hcard
  · exact hdisj
  · -- every edge of `M` lies in the block indexed by its index divided by `s`
    intro x hx
    obtain ⟨j, hj⟩ := he_bij.2 ⟨x, hx⟩
    have hxj : (e j : Sym2 (Fin n)) = x := congrArg Subtype.val hj
    have hlt : j.val / s < 1 + m / s := by
      have h1 : j.val / s ≤ m / s := Nat.div_le_div_right (le_of_lt j.2)
      omega
    refine ⟨⟨j.val / s, hlt⟩, ?_⟩
    rw [edgeSet_fromEdgeSet_of_subset (hS_sub ⟨j.val / s, hlt⟩), ← hxj]
    exact mem_matchBlock.mpr ⟨j, rfl, rfl⟩
  · -- the number of blocks is at most `1 + m / s`
    rw [hm]

end Work.Deep.GKO
