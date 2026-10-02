import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

/-!
# The regularity vocabulary of the GKO chapter

This module starts the *regularity* chapter of `Submission/Work/Deep/GKO/`: the vocabulary and
the elementary counting lemmas on which the engine of the two deep inputs — *a robust expander
of linear minimum degree contains a Hamilton cycle* (`Work.Deep.GKO.HamCycleStatement`) — is
built.

Mathlib already contains Szemerédi's regularity lemma in the equipartition form
(`SimpleGraph.szemeredi_regularity`, `Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean`)
together with `SimpleGraph.IsUniform` and `SimpleGraph.edgeDensity`
(`Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean`).  What this chapter adds is the
*cluster-level* apparatus that the Kühn–Osthus–Treglown argument needs:

* `pairDensity` — the edge density between two vertex sets, as a real number (Mathlib's
  `SimpleGraph.edgeDensity` is rational-valued);
* `IsDenseUniform` — `(A,B)` is `ε`-uniform of density at least `d`;
* `nbrFinset`, `degIn` — the neighbours of a vertex inside a vertex set, and their number;
* `ClusterSystem` — a partition of `Fin n` into `k` indexed classes, and
  `ClusterSystemWithException`, the same with a distinguished exceptional set `V₀`;
* `clusterUnion` — the union of the clusters indexed by a set of indices;
* `reducedGraph` — the reduced graph on the clusters, whose edges are the dense uniform pairs;
* the *degree form of uniformity* (`card_deficient_le`): in an `ε`-uniform pair of density
  `≥ d > ε`, all but at most `ε|B|` vertices of `B` have at least `(d-ε)|X|` neighbours in a
  given `X ⊆ A` with `|X| ≥ ε|A|`.

These are the workhorses of every cluster-level argument; the module uses only narrow Mathlib
imports (see `NarrowImports`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Finset
open Classical

namespace Work.Deep.GKO

noncomputable section

variable {n k : ℕ}

/-! ## Densities of pairs of vertex sets -/

/-- The edge density of `G` between the vertex sets `A` and `B`, as a real number. -/
def pairDensity (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : ℝ :=
  (G.edgeDensity A B : ℝ)

theorem pairDensity_def (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    pairDensity G A B = (#(G.interedges A B) : ℝ) / ((A.card : ℝ) * (B.card : ℝ)) := by
  rw [pairDensity, SimpleGraph.edgeDensity_def]
  push_cast
  rfl

theorem pairDensity_comm (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    pairDensity G A B = pairDensity G B A := by
  simp only [pairDensity, SimpleGraph.edgeDensity_comm]

theorem pairDensity_nonneg (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    0 ≤ pairDensity G A B := by
  simp only [pairDensity]
  exact_mod_cast SimpleGraph.edgeDensity_nonneg (G := G) A B

theorem pairDensity_le_one (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    pairDensity G A B ≤ 1 := by
  simp only [pairDensity]
  exact_mod_cast SimpleGraph.edgeDensity_le_one (G := G) A B

/-- `(A,B)` is **`ε`-uniform of density at least `d`**: Mathlib's regularity condition on the
pair together with a lower bound on its edge density. -/
def IsDenseUniform (G : SimpleGraph (Fin n)) (ε d : ℝ)
    (A B : Finset (Fin n)) : Prop :=
  G.IsUniform ε A B ∧ d ≤ pairDensity G A B

theorem isDenseUniform_comm {G : SimpleGraph (Fin n)} {ε d : ℝ}
    {A B : Finset (Fin n)} (h : IsDenseUniform G ε d A B) : IsDenseUniform G ε d B A :=
  ⟨h.1.symm, by rw [← pairDensity_comm G A B]; exact h.2⟩

theorem IsDenseUniform.mono_density {G : SimpleGraph (Fin n)} {ε d d' : ℝ}
    {A B : Finset (Fin n)} (h : IsDenseUniform G ε d A B) (hdd : d' ≤ d) :
    IsDenseUniform G ε d' A B :=
  ⟨h.1, hdd.trans h.2⟩

theorem IsDenseUniform.mono_eps {G : SimpleGraph (Fin n)} {ε ε' d : ℝ}
    {A B : Finset (Fin n)} (h : IsDenseUniform G ε d A B) (hε : ε ≤ ε') :
    IsDenseUniform G ε' d A B :=
  ⟨h.1.mono hε, h.2⟩

theorem isDenseUniform_zero (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : IsDenseUniform G 1 0 A B :=
  ⟨G.isUniform_one (𝕜 := ℝ), pairDensity_nonneg G A B⟩

/-! ## Neighbour counts into a vertex set -/

/-- The neighbours of `x` inside the vertex set `S`. -/
def nbrFinset (G : SimpleGraph (Fin n)) (x : Fin n)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun y => G.Adj x y

theorem nbrFinset_subset (G : SimpleGraph (Fin n)) (x : Fin n)
    (S : Finset (Fin n)) : nbrFinset G x S ⊆ S :=
  Finset.filter_subset _ _

@[simp]
theorem mem_nbrFinset {G : SimpleGraph (Fin n)} {x y : Fin n}
    {S : Finset (Fin n)} : y ∈ nbrFinset G x S ↔ y ∈ S ∧ G.Adj x y :=
  Finset.mem_filter

/-- The number of neighbours of `x` inside the vertex set `S`. -/
def degIn (G : SimpleGraph (Fin n)) (x : Fin n) (S : Finset (Fin n)) : ℕ :=
  (nbrFinset G x S).card

theorem degIn_le_card (G : SimpleGraph (Fin n)) (x : Fin n)
    (S : Finset (Fin n)) : degIn G x S ≤ S.card :=
  Finset.card_le_card (nbrFinset_subset G x S)

theorem degIn_mono (G : SimpleGraph (Fin n)) (x : Fin n) {S T : Finset (Fin n)}
    (h : S ⊆ T) : degIn G x S ≤ degIn G x T :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem degIn_eq_zero_iff (G : SimpleGraph (Fin n)) (x : Fin n)
    (S : Finset (Fin n)) : degIn G x S = 0 ↔ ∀ y, y ∈ S → ¬ G.Adj x y := by
  rw [degIn, nbrFinset, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- `degIn` is the `ncard` of the set of neighbours of `x` inside `S`, i.e. the form in which
`robustNbrs` counts.  This bridges the regularity vocabulary to `RobustExpander`. -/
theorem degIn_eq_ncard (G : SimpleGraph (Fin n)) (x : Fin n) (S : Finset (Fin n)) :
    degIn G x S = (G.neighborSet x ∩ (S : Set (Fin n))).ncard := by
  classical
  rw [degIn, nbrFinset]
  rw [show G.neighborSet x ∩ (S : Set (Fin n))
        = ((S.filter fun y => G.Adj x y : Finset (Fin n)) : Set (Fin n)) from by
    ext y
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
    tauto]
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext y
  simp [and_comm]

/-- The robust `ν`-neighbourhood of `S` is the set of vertices `x` with `degIn G x S ≥ νn`; this
is the `degIn` form of `robustNbrs`. -/
theorem mem_robustNbrs {G : SimpleGraph (Fin n)} {ν : ℝ} {S : Finset (Fin n)} {x : Fin n} :
    x ∈ robustNbrs G ν S ↔ ν * n ≤ (degIn G x S : ℝ) := by
  rw [degIn_eq_ncard]
  rfl

theorem card_interedges_comm (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : #(G.interedges A B) = #(G.interedges B A) := by
  classical
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp ⊢
    exact ⟨hp.2.1, hp.1, (G.adj_comm _ _).mp hp.2.2⟩
  · intro p _ q _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro q hq
    rw [SimpleGraph.mem_interedges_iff] at hq
    exact ⟨(q.2, q.1), by rw [SimpleGraph.mem_interedges_iff]; exact ⟨hq.2.1, hq.1, (G.adj_comm _ _).mp hq.2.2⟩, rfl⟩

/-- The double-counting identity behind every degree computation with regularity: the number of
edges between `A` and `B` is the sum of the degrees into `B` over `x ∈ A`. -/
theorem sum_degIn_eq_card_interedges (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : ∑ x ∈ A, degIn G x B = #(G.interedges A B) := by
  classical
  rw [SimpleGraph.interedges_def, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [degIn, nbrFinset, Finset.card_filter]

/-- The same identity with the roles of the two vertex sets exchanged. -/
theorem sum_degIn_eq_card_interedges' (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : ∑ y ∈ B, degIn G y A = #(G.interedges A B) := by
  rw [← card_interedges_comm G B A, sum_degIn_eq_card_interedges]

/-! ## The degree form of uniformity -/

/-- **Degree form of `ε`-uniformity.**  If `(A,B)` is `ε`-uniform of density at least `d > ε`,
then for every `X ⊆ A` with `ε|A| ≤ |X|` at most `ε|B|` vertices of `B` have fewer than
`(d-ε)|X|` neighbours in `X`.

This is the single most used consequence of regularity in the cluster-level arguments: it says
that an `ε`-uniform pair of density `≥ d` behaves like a `d`-dense bipartite graph as far as
degrees into large-enough subsets are concerned. -/
theorem card_deficient_le {G : SimpleGraph (Fin n)} {ε d : ℝ}
    {A B X : Finset (Fin n)} (hεd : ε < d) (huni : G.IsUniform ε A B)
    (hdens : d ≤ pairDensity G A B) (hXA : X ⊆ A) (hX : ε * (A.card : ℝ) ≤ (X.card : ℝ)) :
    (((B.filter fun y => (degIn G y X : ℝ) < (d - ε) * (X.card : ℝ)).card : ℕ) : ℝ)
      ≤ ε * (B.card : ℝ) := by
  classical
  set Y : Finset (Fin n) := B.filter fun y => (degIn G y X : ℝ) < (d - ε) * (X.card : ℝ)
  have hεpos : 0 < ε := huni.pos
  have hYsub : Y ⊆ B := Finset.filter_subset _ _
  rcases Y.eq_empty_or_nonempty with hY0 | hYne
  · rw [hY0, Finset.card_empty, Nat.cast_zero]
    nlinarith [Nat.cast_nonneg (α := ℝ) B.card]
  have hXpos : 0 < (X.card : ℝ) := by
    obtain ⟨y, hy⟩ := hYne
    have := (Finset.mem_filter.1 hy).2
    have h0 : (0 : ℝ) ≤ (degIn G y X : ℝ) := Nat.cast_nonneg _
    nlinarith
  by_contra hcon
  have hYbig : (B.card : ℝ) * ε ≤ (Y.card : ℝ) := by
    rw [mul_comm]; exact le_of_lt (lt_of_not_ge hcon)
  have huniform := huni (s' := X) hXA (t' := Y) hYsub (by linarith) hYbig
  -- upper bound for the density of the pair `(X,Y)`
  have hsum : (∑ y ∈ Y, (degIn G y X : ℝ)) < (Y.card : ℝ) * ((d - ε) * (X.card : ℝ)) := by
    have h := Finset.sum_lt_sum_of_nonempty hYne
      (f := fun y => (degIn G y X : ℝ)) (g := fun _ => (d - ε) * (X.card : ℝ))
      (fun y hy => (Finset.mem_filter.1 hy).2)
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hnum : (#(G.interedges X Y) : ℝ) < (Y.card : ℝ) * ((d - ε) * (X.card : ℝ)) := by
    rw [← sum_degIn_eq_card_interedges' G X Y]
    push_cast
    exact hsum
  have hden : (0 : ℝ) < (X.card : ℝ) * (Y.card : ℝ) := by
    have : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.2 hYne.card_pos
    positivity
  have hdensXY : pairDensity G X Y < d - ε := by
    rw [pairDensity_def]
    rw [div_lt_iff₀ hden]
    calc (#(G.interedges X Y) : ℝ)
        < (Y.card : ℝ) * ((d - ε) * (X.card : ℝ)) := hnum
      _ = (d - ε) * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
  have habs : |pairDensity G X Y - pairDensity G A B| < ε := huniform
  have hlt : pairDensity G A B - ε < pairDensity G X Y := by
    have := (abs_lt.1 habs).1; linarith
  have hge : d - ε ≤ pairDensity G A B - ε := by linarith
  linarith [hdensXY, hlt, hge]

/-- Consequence of `card_deficient_le` in the "no neighbours at all" case. -/
theorem card_zero_deg_le {G : SimpleGraph (Fin n)} {ε d : ℝ}
    {A B X : Finset (Fin n)} (hεd : ε < d) (huni : G.IsUniform ε A B)
    (hdens : d ≤ pairDensity G A B) (hXA : X ⊆ A) (hA : 0 < A.card)
    (hX : ε * (A.card : ℝ) ≤ (X.card : ℝ)) :
    (((B.filter fun y => degIn G y X = 0).card : ℕ) : ℝ) ≤ ε * (B.card : ℝ) := by
  classical
  have hεpos : 0 < ε := huni.pos
  have hXpos : 0 < (X.card : ℝ) := by
    have : (0:ℝ) < (A.card : ℝ) := Nat.cast_pos.2 hA
    nlinarith
  have hsub : (B.filter fun y => degIn G y X = 0) ⊆
      (B.filter fun y => (degIn G y X : ℝ) < (d - ε) * (X.card : ℝ)) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, ?_⟩
    rw [hy.2]
    have : (0:ℝ) < (d - ε) * (X.card : ℝ) := by nlinarith
    simpa using this
  have h1 : (((B.filter fun y => degIn G y X = 0).card : ℕ) : ℝ) ≤
      (((B.filter fun y => (degIn G y X : ℝ) < (d - ε) * (X.card : ℝ)).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  linarith [h1, card_deficient_le hεd huni hdens hXA hX]

/-! ## Cluster systems -/

/-- A partition of `Fin n` into `k` indexed clusters together with an **exceptional set** `V₀`:
the clusters are pairwise disjoint and disjoint from `V₀`, and every vertex lies in a cluster or
in `V₀`.

This is the shape in which a regularity partition is used in this chapter.  The clusters are
indexed by `Fin k` so that the reduced graph lives on `Fin k`; `V₀` collects the vertices that
are removed from the cluster structure in the course of the argument (the vertices of "bad"
clusters and the "useless" vertices). -/
structure ClusterSystem (n k : ℕ) where
  /-- the clusters -/
  parts : Fin k → Finset (Fin n)
  /-- distinct clusters are disjoint -/
  disjoint : ∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)
  /-- the exceptional set -/
  exc : Finset (Fin n)
  /-- the exceptional set is disjoint from every cluster -/
  exc_disjoint : ∀ i : Fin k, Disjoint (parts i) exc
  /-- every vertex lies in a cluster or in the exceptional set -/
  covers : ∀ x : Fin n, x ∈ exc ∨ ∃ i : Fin k, x ∈ parts i

namespace ClusterSystem

variable (𝓒 : ClusterSystem n k)

theorem parts_disjoint {i j : Fin k} (h : i ≠ j) : Disjoint (𝓒.parts i) (𝓒.parts j) :=
  𝓒.disjoint i j h

/-- The clusters and the exceptional set have total size `n`. -/
theorem sum_card_parts_add_exc : (∑ i : Fin k, (𝓒.parts i).card) + 𝓒.exc.card = n := by
  classical
  have hcover : (Finset.univ : Finset (Fin n)) ⊆ (Finset.univ.biUnion 𝓒.parts) ∪ 𝓒.exc := by
    intro x _
    rcases 𝓒.covers x with h | ⟨i, hi⟩
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hi⟩)
  have hunion : (Finset.univ : Finset (Fin n)) = (Finset.univ.biUnion 𝓒.parts) ∪ 𝓒.exc :=
    Finset.Subset.antisymm hcover (fun x _ => Finset.mem_univ x)
  have hdisj : Disjoint (Finset.univ.biUnion 𝓒.parts) 𝓒.exc := by
    rw [Finset.disjoint_left]
    intro x hx hxe
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    exact (Finset.disjoint_left.1 (𝓒.exc_disjoint i) hi) hxe
  have h2 : ((Finset.univ : Finset (Fin k)).biUnion 𝓒.parts).card
      = ∑ i : Fin k, (𝓒.parts i).card := by
    rw [Finset.card_biUnion (fun i _ j _ hij => 𝓒.disjoint i j hij)]
  have := congrArg Finset.card hunion
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_union_of_disjoint hdisj, h2] at this
  omega

theorem sum_card_parts_le : ∑ i : Fin k, (𝓒.parts i).card ≤ n := by
  have := 𝓒.sum_card_parts_add_exc; omega

theorem card_le (i : Fin k) : (𝓒.parts i).card ≤ n := by
  have h := 𝓒.sum_card_parts_le
  exact le_trans (Finset.single_le_sum (s := (Finset.univ : Finset (Fin k)))
    (f := fun j : Fin k => (𝓒.parts j).card) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) h

theorem card_parts_mul_le (m : ℕ) (hm : ∀ i, m ≤ (𝓒.parts i).card) : k * m ≤ n := by
  calc k * m = ∑ _i : Fin k, m := by simp
    _ ≤ ∑ i : Fin k, (𝓒.parts i).card := Finset.sum_le_sum fun i _ => hm i
    _ ≤ n := 𝓒.sum_card_parts_le

theorem card_le_card_parts_mul {m : ℕ} (hm : ∀ i, (𝓒.parts i).card ≤ m) : n ≤ k * m + 𝓒.exc.card := by
  calc n = (∑ i : Fin k, (𝓒.parts i).card) + 𝓒.exc.card := 𝓒.sum_card_parts_add_exc.symm
    _ ≤ ∑ _i : Fin k, m + 𝓒.exc.card := by
        exact Nat.add_le_add_right (Finset.sum_le_sum fun i _ => hm i) _
    _ = k * m + 𝓒.exc.card := by simp

theorem mem_unique {x : Fin n} {i j : Fin k} (hi : x ∈ 𝓒.parts i) (hj : x ∈ 𝓒.parts j) : i = j := by
  by_contra h
  exact (Finset.disjoint_left.1 (𝓒.disjoint i j h) hi) hj

/-- The cluster containing `x`, for a vertex known to lie in a cluster. -/
def partOf (x : Fin n) (hx : ∃ i : Fin k, x ∈ 𝓒.parts i) : Fin k := hx.choose

theorem mem_partOf (x : Fin n) (hx : ∃ i : Fin k, x ∈ 𝓒.parts i) :
    x ∈ 𝓒.parts (𝓒.partOf x hx) := hx.choose_spec

theorem notMem_exc_of_mem_part {x : Fin n} {i : Fin k} (hx : x ∈ 𝓒.parts i) : x ∉ 𝓒.exc :=
  fun h => (Finset.disjoint_left.1 (𝓒.exc_disjoint i) hx) h

end ClusterSystem

/-- The union of the clusters indexed by `S`. -/
def clusterUnion (𝓒 : ClusterSystem n k) (S : Finset (Fin k)) : Finset (Fin n) :=
  S.biUnion 𝓒.parts

theorem clusterUnion_card (𝓒 : ClusterSystem n k) (S : Finset (Fin k)) :
    (clusterUnion 𝓒 S).card = ∑ i ∈ S, (𝓒.parts i).card := by
  classical
  rw [clusterUnion, Finset.card_biUnion]
  intro i _ j _ hij
  exact 𝓒.disjoint i j hij

theorem clusterUnion_subset (𝓒 : ClusterSystem n k) (S : Finset (Fin k)) :
    clusterUnion 𝓒 S ⊆ Finset.univ := fun _ _ => Finset.mem_univ _

theorem mem_clusterUnion {𝓒 : ClusterSystem n k} {S : Finset (Fin k)} {x : Fin n} :
    x ∈ clusterUnion 𝓒 S ↔ ∃ i ∈ S, x ∈ 𝓒.parts i := Finset.mem_biUnion

theorem clusterUnion_disjoint_exc (𝓒 : ClusterSystem n k) (S : Finset (Fin k)) :
    Disjoint (clusterUnion 𝓒 S) 𝓒.exc := by
  rw [Finset.disjoint_left]
  intro x hx hxe
  obtain ⟨i, _, hi⟩ := mem_clusterUnion.1 hx
  exact (Finset.disjoint_left.1 (𝓒.exc_disjoint i) hi) hxe

theorem clusterUnion_mono (𝓒 : ClusterSystem n k) {S T : Finset (Fin k)} (h : S ⊆ T) :
    clusterUnion 𝓒 S ⊆ clusterUnion 𝓒 T := by
  intro x hx
  rw [mem_clusterUnion] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, h hi, hxi⟩

theorem clusterUnion_card_eq_mul (𝓒 : ClusterSystem n k) (S : Finset (Fin k)) {m : ℕ}
    (hm : ∀ i ∈ S, (𝓒.parts i).card = m) : (clusterUnion 𝓒 S).card = S.card * m := by
  rw [clusterUnion_card]
  calc ∑ i ∈ S, (𝓒.parts i).card = ∑ _i ∈ S, m := Finset.sum_congr rfl hm
    _ = S.card * m := by rw [Finset.sum_const, smul_eq_mul]

/-! ## The number of non-uniform pairs of clusters -/

/-- The number of ordered pairs of **distinct** clusters that are not `ε`-uniform in `G`.  This is
the quantity that Szemerédi's regularity lemma controls. -/
def nonUniformPairCount (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (ε : ℝ) : ℕ :=
  (((Finset.univ : Finset (Fin k)) ×ˢ Finset.univ).filter
    (fun p : Fin k × Fin k => p.1 ≠ p.2 ∧ ¬ G.IsUniform ε (𝓒.parts p.1) (𝓒.parts p.2))).card

theorem nonUniformPairCount_le_total (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (ε : ℝ) :
    nonUniformPairCount G 𝓒 ε ≤ k * k := by
  classical
  rw [nonUniformPairCount]
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_univ]
  simp

end

end Work.Deep.GKO
