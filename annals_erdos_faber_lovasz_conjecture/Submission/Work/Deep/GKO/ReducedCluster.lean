import Submission.Work.Deep.GKO.RegVocab

/-!
# The reduced graph of a cluster system

This module continues `Work.Deep.GKO.RegVocab`: the vocabulary of the *reduced graph* on the
clusters of a regularity partition, in the two forms the engine needs.

* `UniformPairs G 𝓒 ε` — every pair of distinct clusters is `ε`-uniform in `G`;
* `DenseOrEmptyPairs G 𝓒 d` — every pair of distinct clusters has density `0` or at least `d`.
  This is the property that the *pure graph* of a regularity partition has in the degree form of
  Szemerédi's regularity lemma;
* `denseGraph G 𝓒 d` — the density-based reduced graph on the cluster indices: `i ~ j` iff the
  pair `(V i, V j)` has density at least `d` in `G`.

The reason both notions appear is that the *expansion* arguments (`robustExpander_denseGraph`)
only need `DenseOrEmptyPairs` (an edge between two clusters forces their pair into the reduced
graph), while the *blow-up* arguments need the uniformity of the pairs.

The key elementary consequence is `denseGraph_adj_iff_exists_edge`: under `DenseOrEmptyPairs`,
two clusters are adjacent in `denseGraph G 𝓒 d` iff there is at least one edge of `G` between
them.  This is the form in which the reduced graph is manipulated: a vertex with many neighbours
outside its own cluster is adjacent in the reduced graph to many clusters.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Finset
open Classical

namespace Work.Deep.GKO

noncomputable section

variable {n k : ℕ}

/-! ## Uniformity and density of all pairs of clusters -/

/-- Every pair of distinct clusters of `𝓒` is `ε`-uniform in `G`. -/
def UniformPairs (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k)
    (ε : ℝ) : Prop :=
  ∀ i j : Fin k, i ≠ j → G.IsUniform ε (𝓒.parts i) (𝓒.parts j)

/-- Every pair of distinct clusters of `𝓒` has edge density in `G` equal to `0` or at least
`d`.  (Together with `UniformPairs` this is what the *degree form* of the regularity lemma
produces for its pure graph.) -/
def DenseOrEmptyPairs (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k)
    (d : ℝ) : Prop :=
  ∀ i j : Fin k, i ≠ j → pairDensity G (𝓒.parts i) (𝓒.parts j) ≠ 0 →
    d ≤ pairDensity G (𝓒.parts i) (𝓒.parts j)

/-- **The density reduced graph** of `G` on the clusters of `𝓒`: the clusters `i` and `j` are
adjacent iff the pair `(V i, V j)` has density at least `d`. -/
def denseGraph (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k)
    (d : ℝ) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ d ≤ pairDensity G (𝓒.parts i) (𝓒.parts j)
  symm := Std.Symm.mk fun i j h =>
    ⟨h.1.symm, by rw [← pairDensity_comm G (𝓒.parts i) (𝓒.parts j)]; exact h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem denseGraph_adj {G : SimpleGraph (Fin n)} {𝓒 : ClusterSystem n k}
    {d : ℝ} {i j : Fin k} :
    (denseGraph G 𝓒 d).Adj i j ↔ i ≠ j ∧ d ≤ pairDensity G (𝓒.parts i) (𝓒.parts j) :=
  Iff.rfl

theorem denseGraph_mono {G : SimpleGraph (Fin n)} (𝓒 : ClusterSystem n k)
    {d d' : ℝ} (h : d' ≤ d) : denseGraph G 𝓒 d ≤ denseGraph G 𝓒 d' :=
  fun _ _ hij => ⟨hij.1, h.trans hij.2⟩

/-- Under `DenseOrEmptyPairs`, adjacency in the reduced graph is exactly the existence of an edge
between the two clusters.  This is the arithmetic heart of the passage `G ↦ R`. -/
theorem denseGraph_adj_iff_exists_edge {G : SimpleGraph (Fin n)}
    {𝓒 : ClusterSystem n k} {d : ℝ} (hde : DenseOrEmptyPairs G 𝓒 d) (hd : 0 < d) {i j : Fin k} :
    (denseGraph G 𝓒 d).Adj i j ↔
      i ≠ j ∧ ∃ a ∈ 𝓒.parts i, ∃ b ∈ 𝓒.parts j, G.Adj a b := by
  classical
  constructor
  · rintro ⟨hij, hdens⟩
    refine ⟨hij, ?_⟩
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hzero : #(G.interedges (𝓒.parts i) (𝓒.parts j)) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      obtain ⟨e, he⟩ := Finset.card_pos.1 hpos
      rw [SimpleGraph.mem_interedges_iff] at he
      exact hcon e.1 he.1 e.2 he.2.1 he.2.2
    have : pairDensity G (𝓒.parts i) (𝓒.parts j) = 0 := by
      rw [pairDensity_def, hzero]
      simp
    linarith [hdens, this]
  · rintro ⟨hij, a, ha, b, hb, hab⟩
    refine ⟨hij, hde i j hij ?_⟩
    intro hzero
    have : 0 < pairDensity G (𝓒.parts i) (𝓒.parts j) := by
      rw [pairDensity_def]
      have hmem : (a, b) ∈ G.interedges (𝓒.parts i) (𝓒.parts j) := by
        rw [SimpleGraph.mem_interedges_iff]; exact ⟨ha, hb, hab⟩
      have hpos : 0 < #(G.interedges (𝓒.parts i) (𝓒.parts j)) :=
        Finset.card_pos.2 ⟨_, hmem⟩
      have hpos' : (0 : ℝ) < (#(G.interedges (𝓒.parts i) (𝓒.parts j)) : ℝ) := by exact_mod_cast hpos
      have hden : (0 : ℝ) < ((𝓒.parts i).card : ℝ) * ((𝓒.parts j).card : ℝ) := by
        have h1 : 0 < ((𝓒.parts i).card : ℝ) := by
          exact_mod_cast Finset.card_pos.2 ⟨a, ha⟩
        have h2 : 0 < ((𝓒.parts j).card : ℝ) := by
          exact_mod_cast Finset.card_pos.2 ⟨b, hb⟩
        positivity
      exact div_pos hpos' hden
    linarith

/-- The pairs of the reduced graph are not only dense but also `ε`-uniform.  This is the extra
property the "pure" graph of a regularity partition has: the pairs that survive into the reduced
graph are exactly the pairs that were uniform with density at least `d`. -/
def UniformDensePairs (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (ε d : ℝ) : Prop :=
  ∀ i j : Fin k, i ≠ j → (denseGraph G 𝓒 d).Adj i j → G.IsUniform ε (𝓒.parts i) (𝓒.parts j)

theorem UniformDensePairs.isDenseUniform {G : SimpleGraph (Fin n)} {𝓒 : ClusterSystem n k}
    {ε d : ℝ} (h : UniformDensePairs G 𝓒 ε d) {i j : Fin k} (hij : i ≠ j)
    (hR : (denseGraph G 𝓒 d).Adj i j) : IsDenseUniform G ε d (𝓒.parts i) (𝓒.parts j) :=
  ⟨h i j hij hR, hR.2⟩

/-- **Bad neighbours of a vertex with respect to a reduced graph.**  For a vertex `x` lying in a
cluster `V i`, this counts the neighbours of `x` that lie in clusters `V j` such that the pair
`(i,j)` is *not* an edge of the reduced graph `R`.

This is the quantity that has to be small — for all but `νn/4` vertices — for the reduced graph to
inherit the robust expansion of the ambient graph: only the neighbours of `x` inside clusters
adjacent to `V i` in `R` can make `V i` a robust neighbour in the reduced graph. -/
def badNbrCount (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (R : SimpleGraph (Fin k))
    (x : Fin n) : ℕ :=
  ((((Finset.univ : Finset (Fin k)) ×ˢ Finset.univ).filter
    (fun p : Fin k × Fin k => x ∈ 𝓒.parts p.1 ∧ ¬ R.Adj p.1 p.2)).sum
      (fun p => degIn G x (𝓒.parts p.2)))

/-! ## Neighbours of a vertex in the clusters -/

/-- The clusters (other than the one containing `x`) into which `x` has at least `q` neighbours.
Clusters are compared through their index, so `x`'s own cluster is removed by hand. -/
def denseNbrClusters (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k)
    (i : Fin k) (x : Fin n) (q : ℕ) : Finset (Fin k) :=
  (Finset.univ.erase i).filter fun j => q ≤ degIn G x (𝓒.parts j)

theorem mem_denseNbrClusters {G : SimpleGraph (Fin n)}
    {𝓒 : ClusterSystem n k} {i j : Fin k} {x : Fin n} {q : ℕ} :
    j ∈ denseNbrClusters G 𝓒 i x q ↔ j ≠ i ∧ q ≤ degIn G x (𝓒.parts j) := by
  simp [denseNbrClusters, and_comm]

/-- Every cluster `j ∈ denseNbrClusters G 𝓒 i x q` is adjacent to `i` in the reduced graph (given
`DenseOrEmptyPairs`). -/
theorem denseGraph_adj_of_mem_denseNbrClusters {G : SimpleGraph (Fin n)}
    {𝓒 : ClusterSystem n k} {d : ℝ} (hde : DenseOrEmptyPairs G 𝓒 d) (hd : 0 < d)
    {i j : Fin k} {x : Fin n} {q : ℕ} (hx : x ∈ 𝓒.parts i) (hq : 0 < q)
    (hj : j ∈ denseNbrClusters G 𝓒 i x q) : (denseGraph G 𝓒 d).Adj i j := by
  rw [mem_denseNbrClusters] at hj
  obtain ⟨hji, hdeg⟩ := hj
  rw [denseGraph_adj_iff_exists_edge hde hd]
  refine ⟨fun h => hji h.symm, ?_⟩
  have : 0 < degIn G x (𝓒.parts j) := lt_of_lt_of_le hq hdeg
  obtain ⟨y, hy⟩ := Finset.card_pos.1 this
  rw [mem_nbrFinset] at hy
  exact ⟨x, hx, y, hy.1, hy.2⟩

/-- The degree of `x` into the union of a family of clusters is at most the sum of its degrees
into the individual clusters. -/
theorem degIn_clusterUnion_le_sum (G : SimpleGraph (Fin n))
    (𝓒 : ClusterSystem n k) (x : Fin n) (S : Finset (Fin k)) :
    degIn G x (clusterUnion 𝓒 S) ≤ ∑ j ∈ S, degIn G x (𝓒.parts j) := by
  classical
  have hsub : nbrFinset G x (clusterUnion 𝓒 S) ⊆ S.biUnion fun j => nbrFinset G x (𝓒.parts j) := by
    intro y hy
    rw [mem_nbrFinset] at hy
    obtain ⟨j, hjS, hyj⟩ := mem_clusterUnion.1 hy.1
    rw [Finset.mem_biUnion]
    exact ⟨j, hjS, by rw [mem_nbrFinset]; exact ⟨hyj, hy.2⟩⟩
  calc degIn G x (clusterUnion 𝓒 S)
      ≤ (S.biUnion fun j => nbrFinset G x (𝓒.parts j)).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ S, (nbrFinset G x (𝓒.parts j)).card := Finset.card_biUnion_le
    _ = ∑ j ∈ S, degIn G x (𝓒.parts j) := rfl

/-- **Cluster counting.**  If every cluster has at most `b` vertices and `x` has at least `q`
neighbours in the union of the clusters indexed by `S`, then `x` has a neighbour in at least
`q / b` of those clusters. -/
theorem card_hitClusters_mul_le (G : SimpleGraph (Fin n))
    (𝓒 : ClusterSystem n k) {b q : ℕ} (hb : ∀ j : Fin k, (𝓒.parts j).card ≤ b)
    (x : Fin n) (S : Finset (Fin k)) (hq : q ≤ degIn G x (clusterUnion 𝓒 S)) :
    q ≤ (S.filter fun j => 0 < degIn G x (𝓒.parts j)).card * b := by
  classical
  have h1 : degIn G x (clusterUnion 𝓒 S) ≤ ∑ j ∈ S, degIn G x (𝓒.parts j) :=
    degIn_clusterUnion_le_sum G 𝓒 x S
  have h2 : ∑ j ∈ S, degIn G x (𝓒.parts j)
      = ∑ j ∈ S.filter (fun j => 0 < degIn G x (𝓒.parts j)), degIn G x (𝓒.parts j) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 < degIn G x (𝓒.parts j)
    · simp [h]
    · simp only [h, if_false]
      omega
  have h3 : ∑ j ∈ S.filter (fun j => 0 < degIn G x (𝓒.parts j)), degIn G x (𝓒.parts j)
      ≤ ((S.filter fun j => 0 < degIn G x (𝓒.parts j)).card) * b := by
    calc ∑ j ∈ S.filter (fun j => 0 < degIn G x (𝓒.parts j)), degIn G x (𝓒.parts j)
        ≤ ∑ _j ∈ S.filter (fun j => 0 < degIn G x (𝓒.parts j)), b :=
          Finset.sum_le_sum fun j _ => le_trans (degIn_le_card G x _) (hb j)
      _ = ((S.filter fun j => 0 < degIn G x (𝓒.parts j)).card) * b := by
          rw [Finset.sum_const, smul_eq_mul]
  omega

end

end Work.Deep.GKO
