import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.spanningDefs

/-!
# A union of vertex-disjoint paths is a spanning linear forest with prescribed leaves

Given walks `w i : G.Walk (a i) (b i)` that are paths (`IsPath`), have distinct endpoints
(`a i ≠ b i`), have pairwise disjoint supports, cover all vertices of `G`, and whose endpoints
are exactly the set `L`, the union of the subgraphs of the walks is a spanning linear forest
with leaf set `L`.

The union is `F = ⨆ i, (w i).toSubgraph.spanningCoe`.  Because the supports are disjoint, each
vertex `v` lies in the support of exactly one walk `w i`, and the `F`-neighbours of `v` are
exactly the `w i`-neighbours of `v`; these are computed by `Walk.IsPath.neighborSet_toSubgraph_*`
(one neighbour for an endpoint, two for an interior vertex).  Acyclicity is proved by the
`idxOf`-argument: rotate a hypothetical cycle to start at the vertex of maximal position in
`(w i).support`; both neighbours of that vertex on the cycle must then occupy the preceding
position, hence coincide, contradicting `Walk.IsCycle.snd_ne_penultimate`.
-/

namespace Work.Deep.GKO

open SimpleGraph

/-- For a path `p`, the position of `p.getVert k` in `p.support` is `k`. -/
private theorem walk_support_idxOf_getVert {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) {k : ℕ} (hk : k ≤ p.length) :
    p.support.idxOf (p.getVert k) = k := by
  have hk' : k < p.support.length := by rw [Walk.length_support]; omega
  have hmem : p.getVert k ∈ p.support := Walk.getVert_mem_support p k
  have hidxlt : p.support.idxOf (p.getVert k) < p.support.length :=
    List.idxOf_lt_length_of_mem hmem
  have h1 : p.support[p.support.idxOf (p.getVert k)]'hidxlt = p.support[k]'hk' := by
    rw [List.getElem_idxOf hidxlt, Walk.support_getElem_eq_getVert p hk']
  exact hp.support_nodup.getElem_inj_iff.mp h1

theorem exists_linearForest_of_walks {n m : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (a b : Fin m → Fin n) (w : ∀ i, G.Walk (a i) (b i))
    (hpath : ∀ i, (w i).IsPath) (hend : ∀ i, a i ≠ b i)
    (hdisj : ∀ i j, i ≠ j → ∀ v, v ∈ (w i).support → v ∈ (w j).support → False)
    (hcov : ∀ v : Fin n, ∃ i, v ∈ (w i).support)
    (hL : ∀ v, v ∈ L ↔ ∃ i, v = a i ∨ v = b i) :
    ∃ F : SimpleGraph (Fin n), F ≤ G ∧ Work.Deep.GKO.IsSpanningLinearForestWithLeaves F L := by
  classical
  -- The union of the subgraphs of the walks.
  set F : SimpleGraph (Fin n) := ⨆ i : Fin m, (w i).toSubgraph.spanningCoe with hF
  have hnil : ∀ i, ¬ (w i).Nil := fun i => Walk.not_nil_of_ne (hend i)
  -- Adjacency in `F` is adjacency in one of the walks.
  have F_adj_iff : ∀ u v : Fin n, F.Adj u v ↔ ∃ i, s(u, v) ∈ (w i).edges := by
    intro u v
    rw [hF, SimpleGraph.iSup_adj]
    exact exists_congr (fun i => by rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges])
  -- `F` is a subgraph of `G`.
  have hF_le : F ≤ G := by
    rw [hF]; exact iSup_le (fun i => Subgraph.spanningCoe_le _)
  -- Each vertex lies in the support of at most one walk.
  have h_idx_unique : ∀ (i j : Fin m) (u : Fin n),
      u ∈ (w i).support → u ∈ (w j).support → i = j := by
    intro i j u hi hj
    by_contra h
    exact hdisj i j h u hi hj
  -- The `F`-neighbours of a vertex are the neighbours of the unique walk through it.
  have F_nbr : ∀ (i : Fin m) (u : Fin n), u ∈ (w i).support →
      F.neighborSet u = (w i).toSubgraph.neighborSet u := by
    intro i u hu
    ext y
    rw [SimpleGraph.mem_neighborSet, F_adj_iff, Subgraph.mem_neighborSet]
    constructor
    · rintro ⟨j, hj⟩
      have huj : u ∈ (w j).support := Walk.fst_mem_support_of_mem_edges _ hj
      have hji : j = i := h_idx_unique j i u huj hu
      rw [hji] at hj
      exact Walk.adj_toSubgraph_iff_mem_edges.mpr hj
    · intro hy
      exact ⟨i, Walk.adj_toSubgraph_iff_mem_edges.mp hy⟩
  -- Endpoints of a walk have exactly one neighbour in the union.
  have ncard_start : ∀ i : Fin m, Nat.card (F.neighborSet (a i)) = 1 := by
    intro i
    rw [Nat.card_coe_set_eq, F_nbr i (a i) (Walk.start_mem_support _),
      Walk.IsPath.neighborSet_toSubgraph_startpoint (hpath i) (hnil i)]
    exact Set.ncard_singleton _
  have ncard_end : ∀ i : Fin m, Nat.card (F.neighborSet (b i)) = 1 := by
    intro i
    rw [Nat.card_coe_set_eq, F_nbr i (b i) (Walk.end_mem_support _),
      Walk.IsPath.neighborSet_toSubgraph_endpoint (hpath i) (hnil i)]
    exact Set.ncard_singleton _
  -- Interior vertices of a walk have exactly two neighbours in the union.
  have ncard_int : ∀ (i : Fin m) (k : ℕ), k ≠ 0 → k < (w i).length →
      Nat.card (F.neighborSet ((w i).getVert k)) = 2 := by
    intro i k hk0 hk
    rw [Nat.card_coe_set_eq, F_nbr i _ (Walk.getVert_mem_support _ k)]
    exact Walk.IsPath.ncard_neighborSet_toSubgraph_internal_eq_two (hpath i) hk0 hk
  -- Every vertex is an endpoint or an interior vertex of the unique walk through it.
  have hNF2 : ∀ v : Fin n, Nat.card (F.neighborSet v) ≤ 2 := by
    intro v
    obtain ⟨i, hi⟩ := hcov v
    obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hi
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0] at hkget
      have hv : v = a i := by rw [← hkget, Walk.getVert_zero]
      rw [hv, ncard_start i]
      omega
    · rcases lt_or_eq_of_le hkle with hklt | hkeq
      · have h2 : Nat.card (F.neighborSet v) = 2 := by
          rw [← hkget]; exact ncard_int i k (Nat.pos_iff_ne_zero.mp hk0) hklt
        omega
      · have hv : v = b i := by rw [← hkget, hkeq, Walk.getVert_length]
        rw [hv, ncard_end i]
        omega
  have hNFpos : ∀ v : Fin n, 1 ≤ Nat.card (F.neighborSet v) := by
    intro v
    obtain ⟨i, hi⟩ := hcov v
    obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hi
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0] at hkget
      have hv : v = a i := by rw [← hkget, Walk.getVert_zero]
      rw [hv, ncard_start i]
    · rcases lt_or_eq_of_le hkle with hklt | hkeq
      · have h2 : Nat.card (F.neighborSet v) = 2 := by
          rw [← hkget]; exact ncard_int i k (Nat.pos_iff_ne_zero.mp hk0) hklt
        omega
      · have hv : v = b i := by rw [← hkget, hkeq, Walk.getVert_length]
        rw [hv, ncard_end i]
  have hNFone : ∀ v : Fin n, Nat.card (F.neighborSet v) = 1 ↔ v ∈ L := by
    intro v
    constructor
    · intro h1
      by_contra hv
      obtain ⟨i, hi⟩ := hcov v
      obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hi
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0] at hkget
        exact hv ((hL v).mpr ⟨i, Or.inl (by rw [← hkget, Walk.getVert_zero])⟩)
      · rcases lt_or_eq_of_le hkle with hklt | hkeq
        · have h2 : Nat.card (F.neighborSet v) = 2 := by
            rw [← hkget]; exact ncard_int i k (Nat.pos_iff_ne_zero.mp hk0) hklt
          omega
        · exact hv ((hL v).mpr ⟨i, Or.inr (by rw [← hkget, hkeq, Walk.getVert_length])⟩)
    · intro hv
      obtain ⟨i, hia | hib⟩ := (hL v).mp hv
      · rw [hia, ncard_start i]
      · rw [hib, ncard_end i]
  -- Positions along a walk.
  have idx_getVert : ∀ (i : Fin m) (k : ℕ), k ≤ (w i).length →
      (w i).support.idxOf ((w i).getVert k) = k :=
    fun i k hk => walk_support_idxOf_getVert (hpath i) hk
  -- Adjacent vertices of `F` in a common walk occupy neighbouring positions.
  have F_adj_idx : ∀ (i : Fin m) {u v : Fin n}, u ∈ (w i).support → F.Adj u v →
      ((w i).support.idxOf v = (w i).support.idxOf u + 1 ∨
       (w i).support.idxOf u = (w i).support.idxOf v + 1) := by
    intro i u v hu huv
    obtain ⟨j, hj⟩ := (F_adj_iff u v).mp huv
    have huj : u ∈ (w j).support := Walk.fst_mem_support_of_mem_edges _ hj
    have hji : j = i := h_idx_unique j i u huj hu
    rw [hji] at hj
    obtain ⟨k, hk, heq⟩ := (Walk.mk_mem_edges_iff_exists (w i)).mp hj
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← h2, ← h1, idx_getVert i (k+1) (by omega), idx_getVert i k (by omega)]
    · right
      rw [← h1, ← h2, idx_getVert i (k+1) (by omega), idx_getVert i k (by omega)]
  -- A walk in `F` stays inside a single one of the `w i`.
  have walk_sub : ∀ {u v : Fin n} (c : F.Walk u v) (i : Fin m), u ∈ (w i).support →
      ∀ x ∈ c.support, x ∈ (w i).support := by
    intro u v c
    induction c with
    | nil =>
      intro i hu x hx
      rw [Walk.support_nil, List.mem_singleton] at hx
      rwa [hx]
    | cons hadj q ih =>
      intro i hu x hx
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · obtain ⟨j, hj⟩ := (F_adj_iff _ _).mp hadj
        have hji : j = i := h_idx_unique j i _ (Walk.fst_mem_support_of_mem_edges _ hj) hu
        rw [hji] at hj
        exact ih i (Walk.snd_mem_support_of_mem_edges _ hj) x hx
  -- Acyclicity: rotate a cycle to the vertex of maximal position in its walk.
  have hF_acyc : F.IsAcyclic := by
    intro z c hc
    obtain ⟨i, hi⟩ := hcov z
    have hsub : ∀ x ∈ c.support, x ∈ (w i).support := walk_sub c i hi
    have idx_inj_on : ∀ u x : Fin n, u ∈ (w i).support → x ∈ (w i).support →
        (w i).support.idxOf u = (w i).support.idxOf x → u = x := by
      intro u x hu hx h
      rw [← Walk.getVert_support_idxOf (w i) hu, ← Walk.getVert_support_idxOf (w i) hx, h]
    obtain ⟨z₀, hz₀, hz₀max⟩ := Finset.exists_max_image c.support.toFinset
      (fun x => (w i).support.idxOf x) ⟨z, by simp⟩
    have hz₀mem : z₀ ∈ c.support := List.mem_toFinset.mp hz₀
    have hz₀i : z₀ ∈ (w i).support := hsub z₀ hz₀mem
    have hcyc' : (c.rotate z₀ hz₀mem).IsCycle := Walk.IsCycle.rotate hz₀mem hc
    have hnil' : ¬ (c.rotate z₀ hz₀mem).Nil := hcyc'.not_nil
    have memr : ∀ x : Fin n, x ∈ (c.rotate z₀ hz₀mem).support ↔ x ∈ c.support :=
      fun x => Walk.mem_support_rotate_iff (w := x) c z₀ hz₀mem
    have hsnd : (c.rotate z₀ hz₀mem).snd ∈ c.support :=
      (memr _).mp (Walk.getVert_mem_support _ 1)
    have hpen : (c.rotate z₀ hz₀mem).penultimate ∈ c.support :=
      (memr _).mp (Walk.getVert_mem_support _ ((c.rotate z₀ hz₀mem).length - 1))
    have le_snd : (w i).support.idxOf (c.rotate z₀ hz₀mem).snd ≤ (w i).support.idxOf z₀ :=
      hz₀max _ (List.mem_toFinset.mpr hsnd)
    have le_pen : (w i).support.idxOf (c.rotate z₀ hz₀mem).penultimate ≤ (w i).support.idxOf z₀ :=
      hz₀max _ (List.mem_toFinset.mpr hpen)
    have e1 : (w i).support.idxOf (c.rotate z₀ hz₀mem).snd = (w i).support.idxOf z₀ - 1 := by
      rcases F_adj_idx i hz₀i (Walk.adj_snd hnil') with h | h <;> omega
    have e2 : (w i).support.idxOf (c.rotate z₀ hz₀mem).penultimate
        = (w i).support.idxOf z₀ - 1 := by
      rcases F_adj_idx i (hsub _ hpen) (Walk.adj_penultimate hnil') with h | h <;> omega
    exact hcyc'.snd_ne_penultimate (idx_inj_on _ _ (hsub _ hsnd) (hsub _ hpen) (by omega))
  exact ⟨F, hF_le, hF_acyc, hNFpos, hNF2, hNFone⟩

end Work.Deep.GKO
