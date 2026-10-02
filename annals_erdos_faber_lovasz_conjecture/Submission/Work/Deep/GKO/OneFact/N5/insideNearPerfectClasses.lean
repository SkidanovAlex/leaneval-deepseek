import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.Abs.insideColouring
import Submission.Work.Deep.GKO.RegVocab

/-!
# N5a: the near-perfect inside classes

`insideNearPerfectClasses` (node N5a of `EFL_N5_LEAD.md`) colours the **inside** edges of a graph
`G` on `Fin n` with `d + 1` colours, where `A ⊔ B = univ` splits the vertex set and every vertex of
`A` (resp. `B`) has its number of neighbours inside its own side between `d - t` and `d`.

The construction is the simplest possible one: let `H` be the subgraph of `G` formed by the edges
*inside* `A` or *inside* `B`.  Every degree of `H` is at most `d`, so Vizing's theorem
(`Commons.Combinatorics.SimpleGraph.vizing`) gives a proper edge colouring
`c : Sym2 (Fin n) → Fin (d+1)` of `H`; the colour class `N j` is the graph whose edges are the
`H`-edges of colour `j`.

* each `N j` is a matching and the `N j` are pairwise edge-disjoint (properness and the fact that
  `c` is a function);
* the `N j` cover exactly the inside edges of `G` (`H`'s edge set);
* a vertex `v ∈ A` has `deg_H v ≥ d - t` incident edges, all of different colours, hence it is
  uncovered by at most `(d+1) - (d-t) = t+1` classes.

The last point is the one non-trivial counting step: the colours occurring at `v` inject into the
index set of the classes covering `v`, so `#(covering classes) ≥ deg_H v`.
-/

set_option autoImplicit false

namespace Work.Deep.GKO.OneFact.N5

open Classical

noncomputable section

/-- A vertex lies in `uncov M` exactly when it is in no edge of `M`. -/
lemma mem_uncov {n : ℕ} (M : SimpleGraph (Fin n)) (v : Fin n) :
    v ∈ uncov M ↔ ∀ w, ¬ M.Adj v w := by
  classical
  simp [uncov]

theorem insideNearPerfectClasses {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (G : SimpleGraph (Fin n)) {d t : ℕ}
    (hupA : ∀ v ∈ A, Work.Deep.GKO.degIn G v A ≤ d) (hupB : ∀ v ∈ B, Work.Deep.GKO.degIn G v B ≤ d)
    (hloA : ∀ v ∈ A, d ≤ Work.Deep.GKO.degIn G v A + t)
    (hloB : ∀ v ∈ B, d ≤ Work.Deep.GKO.degIn G v B + t) :
    ∃ N : Fin (d + 1) → SimpleGraph (Fin n),
      (∀ j, Work.Deep.GKO.IsMatching' (N j)) ∧ (∀ j, N j ≤ G) ∧
      (∀ j u v, (N j).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) ∧
      (∀ i j, i ≠ j → Disjoint (N i).edgeSet (N j).edgeSet) ∧
      (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) → ∃ j, (N j).Adj u v) ∧
      (∀ v, (Finset.univ.filter fun j => v ∈ Work.Deep.GKO.OneFact.N5.uncov (N j)).card ≤ t + 1)
:= by
  classical
  -- the "inside" graph: the edges of `G` with both ends on the same side
  have hsymm : ∀ u v : Fin n, (G.Adj u v ∧ ((u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))) →
      (G.Adj v u ∧ ((v ∈ A ∧ u ∈ A) ∨ (v ∈ B ∧ u ∈ B))) := by
    intro u v h
    refine ⟨(G.adj_comm u v).mp h.1, ?_⟩
    rcases h.2 with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨hv, hu⟩
    · exact Or.inr ⟨hv, hu⟩
  let H : SimpleGraph (Fin n) :=
    { Adj := fun u v => G.Adj u v ∧ ((u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
      symm := Std.Symm.mk hsymm
      loopless := Std.Irrefl.mk (fun u h => G.irrefl h.1) }
  have hHadj : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ ((u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) :=
    fun u v => Iff.rfl
  have hmem : ∀ v : Fin n, v ∈ A ∨ v ∈ B := by
    intro v
    have hv : v ∈ A ∪ B := by rw [hcov]; exact Finset.mem_univ v
    exact Finset.mem_union.mp hv
  have hnotB : ∀ v, v ∈ A → v ∉ B := fun v hv hvB => Finset.disjoint_left.mp hAB hv hvB
  have hnotA : ∀ v, v ∈ B → v ∉ A := fun v hv hvA => Finset.disjoint_left.mp hAB hvA hv
  -- the `H`-neighbours of a vertex of `A` are its `G`-neighbours in `A`
  have hHnbrA : ∀ v ∈ A, H.neighborFinset v = Work.Deep.GKO.nbrFinset G v A := by
    intro v hv
    ext w
    rw [SimpleGraph.mem_neighborFinset, Work.Deep.GKO.mem_nbrFinset, hHadj]
    constructor
    · rintro ⟨hG, h | h⟩
      · exact ⟨h.2, hG⟩
      · exact absurd h.1 (hnotB v hv)
    · rintro ⟨hwA, hG⟩
      exact ⟨hG, Or.inl ⟨hv, hwA⟩⟩
  have hHnbrB : ∀ v ∈ B, H.neighborFinset v = Work.Deep.GKO.nbrFinset G v B := by
    intro v hv
    ext w
    rw [SimpleGraph.mem_neighborFinset, Work.Deep.GKO.mem_nbrFinset, hHadj]
    constructor
    · rintro ⟨hG, h | h⟩
      · exact absurd h.1 (hnotA v hv)
      · exact ⟨h.2, hG⟩
    · rintro ⟨hwB, hG⟩
      exact ⟨hG, Or.inr ⟨hv, hwB⟩⟩
  -- every degree of `H` is at most `d`
  have hHdeg : ∀ v : Fin n, Nat.card (H.neighborSet v) ≤ d := by
    intro v
    rcases hmem v with hv | hv
    · rw [Commons.Combinatorics.SimpleGraph.natcard_neighborSet_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree, hHnbrA v hv]
      simpa [Work.Deep.GKO.degIn] using hupA v hv
    · rw [Commons.Combinatorics.SimpleGraph.natcard_neighborSet_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree, hHnbrB v hv]
      simpa [Work.Deep.GKO.degIn] using hupB v hv
  have hmax : H.maxDegree ≤ d := H.maxDegree_le_of_forall_degree_le d (fun v => by
    rw [← Commons.Combinatorics.SimpleGraph.natcard_neighborSet_eq_degree]
    exact hHdeg v)
  have hle : H.maxDegree + 1 ≤ d + 1 := by omega
  have hnezero : NeZero (d + 1) := ⟨Nat.succ_ne_zero d⟩
  -- Vizing: a proper edge colouring of `H` with `d + 1` colours
  obtain ⟨c, hc⟩ := Commons.Combinatorics.SimpleGraph.exists_isProper_of_colorable H
    (SimpleGraph.Colorable.mono hle (Commons.Combinatorics.SimpleGraph.vizing H))
  have hproper : ∀ e ∈ H.edgeSet, ∀ e' ∈ H.edgeSet, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') →
      c e ≠ c e' := fun e he e' he' hne hadj =>
    hc e (SimpleGraph.mem_edgeFinset.mpr he) e' (SimpleGraph.mem_edgeFinset.mpr he') hne hadj
  -- the colour classes
  let N : Fin (d + 1) → SimpleGraph (Fin n) :=
    fun j => SimpleGraph.fromEdgeSet {e | e ∈ H.edgeSet ∧ c e = j}
  have hNadj : ∀ j u v, (N j).Adj u v ↔ H.Adj u v ∧ c s(u,v) = j := by
    intro j u v
    show (SimpleGraph.fromEdgeSet {e | e ∈ H.edgeSet ∧ c e = j}).Adj u v ↔ _
    rw [SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      exact ⟨(SimpleGraph.mem_edgeSet H).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(SimpleGraph.mem_edgeSet H).mpr h1, h2⟩, H.ne_of_adj h1⟩
  refine ⟨N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- each colour class is a matching
  · intro j v w w' hvw hvw'
    rw [hNadj j v w] at hvw
    rw [hNadj j v w'] at hvw'
    by_contra hne
    have hse : s(v,w) ≠ s(v,w') := fun h =>
      hne (Commons.Combinatorics.SimpleGraph.Vizing.sym2_mk_left_injective v h)
    exact hproper (s(v,w)) ((SimpleGraph.mem_edgeSet H).mpr hvw.1) (s(v,w'))
      ((SimpleGraph.mem_edgeSet H).mpr hvw'.1) hse
      ⟨v, Sym2.mem_mk_left v w, Sym2.mem_mk_left v w'⟩ (hvw.2.trans hvw'.2.symm)
  -- each colour class is a subgraph of `G`
  · intro j
    rw [SimpleGraph.le_iff_adj]
    intro u v huv
    rw [hNadj j u v] at huv
    exact ((hHadj u v).mp huv.1).1
  -- each colour class consists of inside edges
  · intro j u v huv
    rw [hNadj j u v] at huv
    exact ((hHadj u v).mp huv.1).2
  -- different colours give edge-disjoint classes
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    have hi : c e = i := by
      have h1 : e ∈ (SimpleGraph.fromEdgeSet {x | x ∈ H.edgeSet ∧ c x = i}).edgeSet := hei
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h1
      exact (((Set.mem_sdiff e).mp h1).1).2
    have hj : c e = j := by
      have h1 : e ∈ (SimpleGraph.fromEdgeSet {x | x ∈ H.edgeSet ∧ c x = j}).edgeSet := hej
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h1
      exact (((Set.mem_sdiff e).mp h1).1).2
    exact hij (hi.symm.trans hj)
  -- every inside edge is covered
  · intro u v hG hins
    refine ⟨c s(u,v), ?_⟩
    rw [hNadj (c s(u,v)) u v]
    exact ⟨(hHadj u v).mpr ⟨hG, hins⟩, rfl⟩
  -- every vertex is uncovered by at most `t + 1` classes
  · intro v
    have hX : d ≤ (H.neighborFinset v).card + t := by
      rcases hmem v with hv | hv
      · rw [hHnbrA v hv]
        simpa [Work.Deep.GKO.degIn] using hloA v hv
      · rw [hHnbrB v hv]
        simpa [Work.Deep.GKO.degIn] using hloB v hv
    -- the colours occurring at `v` are the classes covering `v`
    have hinjOn : Set.InjOn (fun w : Fin n => c s(v,w)) ↑(H.neighborFinset v) := by
      intro a ha b hb hab
      have hAa : H.Adj v a := (SimpleGraph.mem_neighborFinset H v a).mp ha
      have hAb : H.Adj v b := (SimpleGraph.mem_neighborFinset H v b).mp hb
      by_contra hne
      have hse : s(v,a) ≠ s(v,b) := fun h =>
        hne (Commons.Combinatorics.SimpleGraph.Vizing.sym2_mk_left_injective v h)
      exact hproper (s(v,a)) ((SimpleGraph.mem_edgeSet H).mpr hAa) (s(v,b))
        ((SimpleGraph.mem_edgeSet H).mpr hAb) hse
        ⟨v, Sym2.mem_mk_left v a, Sym2.mem_mk_left v b⟩ hab
    have hUX : (H.neighborFinset v).card ≤
        (Finset.univ.filter fun j => v ∉ Work.Deep.GKO.OneFact.N5.uncov (N j)).card := by
      have hsub : (H.neighborFinset v).image (fun w => c s(v,w)) ⊆
          (Finset.univ.filter fun j => v ∉ Work.Deep.GKO.OneFact.N5.uncov (N j)) := by
        intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨w, hwX, rfl⟩ := hj
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hAdj : H.Adj v w := (SimpleGraph.mem_neighborFinset H v w).mp hwX
        intro huncov
        rw [mem_uncov] at huncov
        exact huncov w ((hNadj (c s(v,w)) v w).mpr ⟨hAdj, rfl⟩)
      calc (H.neighborFinset v).card
          = ((H.neighborFinset v).image (fun w => c s(v,w))).card :=
            (Finset.card_image_of_injOn hinjOn).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hTU : (Finset.univ.filter fun j => v ∈ Work.Deep.GKO.OneFact.N5.uncov (N j)).card
        + (Finset.univ.filter fun j => v ∉ Work.Deep.GKO.OneFact.N5.uncov (N j)).card
          = d + 1 := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (d+1))))
        (p := fun j => v ∈ Work.Deep.GKO.OneFact.N5.uncov (N j))
      simpa using this
    omega

end

end Work.Deep.GKO.OneFact.N5
