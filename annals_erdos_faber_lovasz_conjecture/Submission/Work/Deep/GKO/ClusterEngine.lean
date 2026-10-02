import Submission.Work.Deep.GKO.ReducedCluster
import Submission.Work.Deep.GKO.HamCycleInput

/-!
# The cluster engine: from a robust expander to a Hamilton cycle

`Work.Deep.GKO.HamCycleStatement` (`HamCycleInput.lean`) is the engine of the two deep inputs of
this chapter: *a robust expander of linear minimum degree contains a Hamilton cycle*
(Kühn–Osthus–Treglown).  This module records the *shape* of the engine's proof and reduces it to
two named cluster-level statements, in the same style in which `KOInputs.lean` reduces
`KOStatement` to its two tools.

## The route (Kühn–Osthus–Treglown §4, with Keevash–Kühn–Osthus for the blow-up)

1. **Clustering** (`ClusterReductionStatement`): apply Szemerédi's regularity lemma to `G` (the
   effective equipartition form is in Mathlib, `SimpleGraph.szemeredi_regularity`, and the bridge
   to the vocabulary of this chapter is `Work.Deep.GKO.exists_clusterSystem`); delete the edges
   between pairs of clusters that are not regular or have small density, to obtain a *pure*
   subgraph `G'` and a partition into equal clusters plus a small exceptional set; the density
   reduced graph `R` of `G'` is then again a robust expander with linear minimum degree — this is
   `work.Deep.GKO.robustExpander_denseGraph`, the undirected form of Kühn–Osthus–Treglout's
   `robustR`.
2. **Induction**: apply the engine to `R` (a graph on `k < n` vertices) to get a **Hamilton cycle
   of the reduced graph** — a cyclic order of the clusters along which the blow-up is performed.
3. **Blow-up** (`FindCycleStatement`): given the cluster system, the reduced graph `R`, a Hamilton
   cycle `Cyc` of `R` and the exceptional vertices, the ambient graph has a Hamilton cycle.  The
   proof is the argument of Keevash–Kühn–Osthus's `find-cycle` lemma: first remove the vertices
   of a cluster that have too few neighbours in its two cycle-neighbours (this is
   `Work.Deep.GKO.card_deficient_le`), then construct a *balanced walk* in `R` visiting every
   cluster and every exceptional vertex, map it to a Hamilton cycle of the auxiliary graph in
   which each dense pair is replaced by a complete bipartite graph, and finally transfer that
   cycle back with a blow-up lemma for cycles (`card_useless_le`, `card_deficient_le` and the
   restriction lemmas `IsDenseUniform.restrict`/`IsSuperregularPair.restrict` are its ingredients).

Both steps are *cluster-level* combinatorics: no further regularity theory is needed beyond
Mathlib's.

## Contents

* `IsSuperregularPair` — an `ε`-uniform pair of density `≥ d` in which every vertex has at least
  `d·|B|` neighbours on the other side (the notion along the cycle of clusters).
* `ClusterReductionStatement` — step 1.
* `FindCycleStatement` — step 3.
* `hamCycleStatement_of_clusterReduction_and_findCycle` — the *assembly*: the two steps above
  imply the chapter's engine `HamCycleStatement` (`HamCycleInput.lean`).  There is no recursion;
  the range parameter of the reduction is chosen small in terms of the minimum-degree fraction,
  which is the hierarchy `ν ≤ τ ≪ η` of Kühn–Osthus–Treglown's Theorem 4.1.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Finset
open Classical

namespace Work.Deep.GKO

noncomputable section

variable {n k : ℕ}

/-! ## Superregular pairs -/

/-- A pair `(A,B)` is **`(ε,d)`-superregular** if it is `ε`-uniform of density at least `d` and
every vertex of `A` (resp. `B`) has at least `d·|B|` (resp. `d·|A|`) neighbours on the other side.
This is the condition on the pairs of clusters that are used by the blow-up step: along the cycle
of clusters, every vertex has many neighbours in its neighbouring clusters. -/
def IsSuperregularPair (G : SimpleGraph (Fin n)) (ε d : ℝ) (A B : Finset (Fin n)) : Prop :=
  IsDenseUniform G ε d A B ∧
    (∀ x ∈ A, d * (B.card : ℝ) ≤ (degIn G x B : ℝ)) ∧
    (∀ y ∈ B, d * (A.card : ℝ) ≤ (degIn G y A : ℝ))

theorem IsSuperregularPair.isDenseUniform {G : SimpleGraph (Fin n)} {ε d : ℝ}
    {A B : Finset (Fin n)} (h : IsSuperregularPair G ε d A B) : IsDenseUniform G ε d A B :=
  h.1

theorem isSuperregularPair_comm {G : SimpleGraph (Fin n)} {ε d : ℝ} {A B : Finset (Fin n)}
    (h : IsSuperregularPair G ε d A B) : IsSuperregularPair G ε d B A :=
  ⟨isDenseUniform_comm h.1, h.2.2, h.2.1⟩

/-- Superregularity is monotone in the density threshold and in the uniformity parameter. -/
theorem IsSuperregularPair.mono {G : SimpleGraph (Fin n)} {ε ε' d d' : ℝ}
    {A B : Finset (Fin n)} (h : IsSuperregularPair G ε d A B) (hε : ε ≤ ε') (hd : d' ≤ d) :
    IsSuperregularPair G ε' d' A B :=
  ⟨h.1.mono_eps hε |>.mono_density hd,
    fun x hx => le_trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)) (h.2.1 x hx),
    fun y hy => le_trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)) (h.2.2 y hy)⟩

/-- A spanning `2`-factor: a `2`-regular spanning subgraph (a disjoint union of cycles, with
`2`-cycles allowed as doubly-used edges).  This is the undirected analogue of the `1`-factor of a
digraph that Keevash–Kühn–Osthus's blow-up lemma takes as a hypothesis: it organises the clusters
into cycles along which the balanced walk runs. -/
def IsTwoFactor (F : SimpleGraph (Fin k)) : Prop := ∀ v : Fin k, Nat.card (F.neighborSet v) = 2

theorem isTwoFactor_symm {F : SimpleGraph (Fin k)} (h : IsTwoFactor F) (v : Fin k) :
    Nat.card (F.neighborSet v) = 2 := h v

/-- A **cycle cover** of a graph: a permutation sending every vertex to a neighbour.  Equivalently,
a `1`-factor of the bipartite double cover of `R`, i.e. a spanning subgraph in which every vertex
has out-degree and in-degree one, *2-cycles allowed*.

This — not a simple `2`-factor (`IsTwoFactor`) — is what the balanced-walk step of the blow-up
consumes, and it is what Hall's theorem provides (see `NOTES_ENGINE.md` §3.3: a simple `2`-factor
can fail even for a robust expander with linear minimum degree and the plain expansion, as the
"star of two cliques" of `Work.Deep.GKO.not_exists_twoFactor_of_robustExpander` shows). -/
def IsCycleCover (R : SimpleGraph (Fin k)) (σ : Fin k ≃ Fin k) : Prop := ∀ i : Fin k, R.Adj i (σ i)

/-- The **plain neighbourhood** of a set of vertices of a graph, as a finset: the vertices
adjacent to at least one vertex of `S`.  This is the form of neighbourhood expansion that the
balanced-walk step of the blow-up uses (it is weaker than `robustNbrs`, and for sets of size
`≥ τk` it follows from robust expansion, while for smaller sets it follows from the linear minimum
degree of the reduced graph). -/
def nbrUnion (G : SimpleGraph (Fin k)) (S : Finset (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter fun j => ∃ i ∈ S, G.Adj i j

theorem mem_nbrUnion {G : SimpleGraph (Fin k)} {S : Finset (Fin k)} {j : Fin k} :
    j ∈ nbrUnion G S ↔ ∃ i ∈ S, G.Adj i j := by
  simp [nbrUnion]

/-! ### Orbits of a cycle cover

The blow-up step of the engine (`FindCycleStatement`) runs along a cycle cover `σ` of the reduced
graph `R`: it decomposes `[k]` into the cycles ("rides") of `σ` and winds around each of them.  The
visit counts of the walk that does the winding are counted per orbit, so the number of orbits
matters: the blow-up is called with a cycle cover all of whose orbits are *short*, which is what
`Work.Deep.GKO.BoundedCycleCoverStatement` provides. -/

/-- The **`σ`-orbit** of a vertex `i`: the set of vertices reachable from `i` by iterating the
permutation `σ`.  For a cycle cover `σ` of a graph it is the cycle of `σ` through `i`. -/
def orbitFinset {k : ℕ} (σ : Fin k ≃ Fin k) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => ∃ r : ℕ, σ^[r] i = j

theorem mem_orbitFinset {k : ℕ} (σ : Fin k ≃ Fin k) {i j : Fin k} :
    j ∈ orbitFinset σ i ↔ ∃ r : ℕ, σ^[r] i = j := by
  simp [orbitFinset]

theorem self_mem_orbitFinset {k : ℕ} (σ : Fin k ≃ Fin k) (i : Fin k) :
    i ∈ orbitFinset σ i := by
  rw [mem_orbitFinset]
  exact ⟨0, rfl⟩

/-- A vertex and its successor lie in the same orbit. -/
theorem orbitFinset_succ_subset {k : ℕ} (σ : Fin k ≃ Fin k) (i : Fin k) :
    orbitFinset σ (σ i) ⊆ orbitFinset σ i := by
  intro j hj
  rw [mem_orbitFinset] at hj ⊢
  obtain ⟨r, hr⟩ := hj
  refine ⟨r + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  exact hr

/-! ## Step 1: the clustering -/

/-- **The clustering step of the engine.**  Given `α, ν, τ` and a small `c` (the minimum-degree
parameter of the reduced graph) and a lower bound `K` on the number of clusters (which the blow-up
step dictates), a robust expander `G` of minimum degree `αn` has a *pure* subgraph `G' ≤ G` and a
partition into `k ≥ K` equal clusters of size `m` plus an exceptional set `V₀` (of size
`≤ εp·n`) such that:

* `G'` has no edges inside a cluster and no edges between pairs of clusters that are not adjacent in
  a graph `R` on the clusters;
* the pairs of `R` are `εp`-uniform of density `≥ dp` in `G'`;
* the exceptional vertices have `≥ c·m` neighbours in some cluster;
* `R` has a cycle cover `σ`, minimum degree `≥ (α/2)k`, plain neighbourhood expansion with parameter
  `c`, and is again a robust expander (robustness `ν₁ ≥ min (ν/8) (α/4)`, range `2τ`).

The numbers `K` and `M` are *parameters* of the conclusion (`∀ K M, ∃ k₀ k₁ n₀, ...`), i.e. the
thresholds may depend on them: the cluster system must have at least `K` clusters and each cluster
at least `M` vertices inside `n` vertices, so `n` must be allowed to depend on `K` and `M`.  The
extra witness `k₁` is the upper bound `k ≤ k₁` on the number of clusters that the effective form of
Szemerédi's regularity result provides (`k ≤ SzemerediRegularity.bound ε₀ l`, see
`Work.Deep.GKO.exists_clusterSystem`); together with `M ≤ m` it is what the blow-up needs (the
uniformity and density hypotheses of the pairs are only meaningful when the clusters are large, and
`find-cycle`'s condition `2|V₀| ≤ d·m` is met only when there are not too many clusters).

The hierarchy `4τ + c ≤ α/2` is not an artefact: the plain-expansion clause is *derived* from the
linear minimum degree `(α/2)k` of `R` and the robustness of `R` at range `2τ`, by the elementary
three-regime argument recorded in
`Work.Deep.GKO.plainExpansion_of_robustExpander` (whose hypothesis is `τ₀ + c ≤ δ`, with `τ₀` the
robustness range and `δ` the minimum-degree fraction; here `τ₀ = 2τ` and `δ = α/2`).  This mirrors
the hierarchy `ν ≤ τ ≪ η` of Kühn–Osthus–Treglown's Theorem 4.1, where `η` is the minimum-degree
fraction and `τ` the range.

This is Szemerédi's regularity lemma (Mathlib: `SimpleGraph.szemeredi_regularity`, bridged by
`Work.Deep.GKO.exists_clusterSystem`) followed by the *degree form* (the cleaning: deleting the
edges of pairs that are not regular or of density below `d`, the step with the delicate bookkeeping —
see `NOTES_ENGINE.md` §5), then `Work.Deep.GKO.robustExpander_of_degreeLoss` (the loss of the
deleted edges) and `Work.Deep.GKO.robustExpander_of_badNbrCount_exc` (the transfer of robustness and
of the linear minimum degree to `R`), and finally the cycle cover
`Work.Deep.GKO.exists_cycleCover_of_robustExpander` (Hall's theorem in the bipartite double cover;
`NOTES_ENGINE.md` §3.3 records why a *cycle cover* and not a `2`-factor is what the blow-up
consumes). -/
def ClusterReductionStatement : Prop :=
  ∀ α ν τ c : ℝ, 0 < α → 0 < ν → ν ≤ α → ν ≤ τ → τ ≤ 1 / 8 →
    4 * τ + c ≤ α / 2 →
    0 < c → c ≤ 1 / 4 → c ≤ ν / 8 → c ≤ α / 8 →
    ∃ εp dp : ℝ, 0 < εp ∧ εp ≤ dp ∧ 128 * εp ≤ dp ∧ dp ≤ c ∧ εp ≤ c ^ 2 / 10 ^ 6 ∧
      ∀ K M : ℕ, ∃ k₀ k₁ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
        RobustExpander G ν τ →
        (∀ x : Fin n, α * (n : ℝ) ≤ (Nat.card (G.neighborSet x) : ℝ)) →
        ∃ (k m : ℕ) (𝓒 : ClusterSystem n k) (G' : SimpleGraph (Fin n))
          (R : SimpleGraph (Fin k)) (ν₁ : ℝ),
          K ≤ k ∧ k ≤ k₁ ∧ M ≤ m ∧ 1 ≤ m ∧ 0 < ν₁ ∧ min (ν / 8) (α / 4) ≤ ν₁ ∧ c ≤ ν₁ ∧ ν₁ ≤ τ ∧ (∀ i : Fin k, (𝓒.parts i).card = m) ∧
          (((𝓒.exc.card : ℕ) : ℝ) ≤ εp * (n : ℝ)) ∧
          G' ≤ G ∧
          (∀ i : Fin k, ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts i, ¬ G'.Adj x y) ∧
          (∀ i j : Fin k, i ≠ j → ¬ R.Adj i j →
            ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts j, ¬ G'.Adj x y) ∧
          (∀ i j : Fin k, i ≠ j → R.Adj i j →
            IsDenseUniform G' εp dp (𝓒.parts i) (𝓒.parts j)) ∧
          (∀ x ∈ 𝓒.exc, ∃ i : Fin k, c * (m : ℝ) ≤ (degIn G' x (𝓒.parts i) : ℝ)) ∧
          (∃ σ : Fin k ≃ Fin k, IsCycleCover R σ) ∧
          RobustExpander R ν₁ (2 * τ) ∧
          (∀ i : Fin k, α / 2 * (k : ℝ) ≤ (Nat.card (R.neighborSet i) : ℝ)) ∧
          (∀ S : Finset (Fin k), c * (k : ℝ) ≤ (S.card : ℝ) →
            (S.card : ℝ) ≤ (1 - c) * (k : ℝ) →
            (S.card : ℝ) + c * (k : ℝ) ≤ ((nbrUnion R S).card : ℝ)) ∧
          (∀ x : Fin n, (Nat.card (G.neighborSet x) : ℝ) ≤
            (Nat.card (G'.neighborSet x) : ℝ) + 256 * εp * (n : ℝ))
/-- **The bounded cycle cover of the reduced graph.**  The blow-up of the engine runs along a
cycle cover `σ` of `R` and winds around its orbits; the number of orbits has to be large (i.e. the
orbits short) so that the *visit counts* of the blow-up's walk stay below the cluster size.  This
statement records the needed supply: a graph of minimum degree `≥ 2ck` with the plain expansion has
a cycle cover all of whose orbits have length `≤ ⌈8/c⌉`.

See `Submission/Work/Deep/GKO/NOTES_BLOWUP.md` §8.5 for the intended proof (the greedy removal of
short cycles, whose existence is the Moore/girth bound, followed by the absorption of the leftover
vertices into the cycles found). -/
def BoundedCycleCoverStatement : Prop :=
  ∀ (k : ℕ) (R : SimpleGraph (Fin k)) (c : ℝ), 0 < c → c ≤ 1 / 4 → (2 / c) ^ 10 ≤ (k : ℝ) →
    (∀ i : Fin k, 2 * c * (k : ℝ) ≤ (Nat.card (R.neighborSet i) : ℝ)) →
    (∀ S : Finset (Fin k), c * (k : ℝ) ≤ (S.card : ℝ) →
      (S.card : ℝ) ≤ (1 - c) * (k : ℝ) →
      (S.card : ℝ) + c * (k : ℝ) ≤ ((nbrUnion R S).card : ℝ)) →
    ∃ σ : Fin k ≃ Fin k, IsCycleCover R σ ∧ ∀ i : Fin k, (orbitFinset σ i).card ≤ ⌈8 / c⌉₊

/-! ## Step 3: the blow-up along a `2`-factor of the reduced graph -/

/-- **The blow-up step of the engine** (Keevash–Kühn–Osthus' `find-cycle` lemma, in the undirected
form used here).  Let `G` be a graph with no edges inside a cluster and no edges between pairs of
clusters that are not adjacent in a graph `R` on the cluster indices.  Let the vertex set be
partitioned into equal clusters of size `m` and an exceptional set of size at most `εn`, let
`Cyc ⊆ R` be a spanning `2`-factor of `R`, suppose that `R` is a robust `(ν₀,τ₀)`-expander with
minimum degree `≥ 2ck` and plain neighbourhood expansion with parameter `c`, that the pairs of `R`
are `ε`-uniform of density at least `d`, and that every exceptional vertex has at least `c·m`
neighbours in some cluster.  Then `G` has a Hamilton cycle.

The proof (see `NOTES_ENGINE.md` §2 and §3.4): refine the clusters so that the pairs of `Cyc` are
superregular (`exists_superregularCycleClusterSystem`); construct a closed *balanced* walk in `R`
visiting every cluster at least once and at most `√ε n` times and every exceptional vertex once;
map it to a Hamilton cycle of the auxiliary graph in which each pair of `R` is replaced by a
complete bipartite graph; and transfer that cycle back to `G` with the blow-up argument for cycles
(`hamiltPath_in_superregularPair`), using the buffer sets of KKO. -/
def FindCycleStatement : Prop :=
  ∀ ε d c ν₀ τ₀ : ℝ, 0 < ε → ε ≤ d → d ≤ c → c ≤ 1 / 4 → 0 < ν₀ → ν₀ ≤ τ₀ → c ≤ ν₀ →
    ∃ k₀ M₀ n₀ : ℕ, ∀ k ≥ k₀, ∀ n ≥ n₀, ∀ m : ℕ, M₀ ≤ m →
      ∀ (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (R : SimpleGraph (Fin k))
        (σ : Fin k ≃ Fin k),
        (∀ i : Fin k, (𝓒.parts i).card = m) →
        ((𝓒.exc.card : ℕ) : ℝ) ≤ ε * (n : ℝ) →
        (∀ i : Fin k, ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts i, ¬ G.Adj x y) →
        (∀ i j : Fin k, i ≠ j → ¬ R.Adj i j →
          ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts j, ¬ G.Adj x y) →
        (∀ i j : Fin k, i ≠ j → R.Adj i j →
          IsDenseUniform G ε d (𝓒.parts i) (𝓒.parts j)) →
        IsCycleCover R σ →
        RobustExpander R ν₀ τ₀ →
        (∀ i : Fin k, 2 * c * (k : ℝ) ≤ (Nat.card (R.neighborSet i) : ℝ)) →
        (∀ S : Finset (Fin k), c * (k : ℝ) ≤ (S.card : ℝ) →
          (S.card : ℝ) ≤ (1 - c) * (k : ℝ) →
          (S.card : ℝ) + c * (k : ℝ) ≤ ((nbrUnion R S).card : ℝ)) →
        (∀ x ∈ 𝓒.exc, ∃ i : Fin k, c * (m : ℝ) ≤ (degIn G x (𝓒.parts i) : ℝ)) →
        ∃ C : SimpleGraph (Fin n), C ≤ G ∧ IsHamiltonCycle' C

/-- **The blow-up step of the engine, faithful form.**  Same conclusion as `FindCycleStatement`,
with the hypotheses the proof actually needs (see `NOTES_BLOWUP.md` §8):

* the pairs of `σ` are **superregular** (the winding goes along the `σ`-orbits, so the blow-up
  lemma's condition (C8) needs superregularity along them) — supplied by refining the clusters
  with `Work.Deep.GKO.exists_superregularPermClusterSystem` before the blow-up is applied;
* the orbits of `σ` are shorter than `⌈8/c⌉` (`BoundedCycleCoverStatement`) and the visit counts
  of the walk produced by the drive are bounded by the last hypothesis
  `8·⌈8/c⌉·|exc|·(⌈1/c⌉+5) ≤ k·m`: the walk `W` visits every cluster at most
  `8·⌈8/c⌉·|exc|·(⌈1/c⌉+5)` times, which is `≤ m/2` — the bound the *buffer sets* `J_i` of the
  construction need (the constant `m/10` of Keevash--Kühn--Osthus is not needed: their greedy works
  with any positive fraction of `m`);
* the **balanced attachment**: every exceptional vertex has an attachment cluster with `c·m`
  neighbours *and* the attachments are balanced, `2·Q_i ≤ m` (which is what makes the blow-up
  lemma's condition (C4) hold with a constant `K₂`; without balance (C4) would force `|exc| ≪ m`,
  a `1/k` hierarchy — see `NOTES_BLOWUP.md` §8.3).

The reduction supplies all three (`ClusterReductionStatement`'s conclusion, plus
`BoundedCycleCoverStatement` applied to `R`, plus the refinement step). -/
def FindCycleStatementFixed : Prop :=
  ∀ ε d c ν₀ τ₀ : ℝ, 0 < ε → ε ≤ d → d ≤ c → c ≤ 1 / 4 → 0 < ν₀ → ν₀ ≤ τ₀ → c ≤ ν₀ →
    ∃ k₀ M₀ n₀ : ℕ, ∀ k ≥ k₀, ∀ n ≥ n₀, ∀ m : ℕ, M₀ ≤ m →
      ∀ (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (R : SimpleGraph (Fin k))
        (σ : Fin k ≃ Fin k),
        (∀ i : Fin k, (𝓒.parts i).card = m) →
        ((𝓒.exc.card : ℕ) : ℝ) ≤ ε * (n : ℝ) →
        (∀ i : Fin k, ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts i, ¬ G.Adj x y) →
        (∀ i j : Fin k, i ≠ j → ¬ R.Adj i j →
          ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts j, ¬ G.Adj x y) →
        (∀ i j : Fin k, i ≠ j → R.Adj i j →
          IsDenseUniform G ε d (𝓒.parts i) (𝓒.parts j)) →
        (∀ i : Fin k, IsSuperregularPair G ε d (𝓒.parts i) (𝓒.parts (σ i))) →
        IsCycleCover R σ →
        RobustExpander R ν₀ τ₀ →
        (∀ i : Fin k, 2 * c * (k : ℝ) ≤ (Nat.card (R.neighborSet i) : ℝ)) →
        (∀ S : Finset (Fin k), c * (k : ℝ) ≤ (S.card : ℝ) →
          (S.card : ℝ) ≤ (1 - c) * (k : ℝ) →
          (S.card : ℝ) + c * (k : ℝ) ≤ ((nbrUnion R S).card : ℝ)) →
        (∀ i : Fin k, (orbitFinset σ i).card ≤ ⌈8 / c⌉₊) →
        (∃ att : Fin n → Fin k,
          (∀ x ∈ 𝓒.exc, c * (m : ℝ) ≤ (degIn G x (𝓒.parts (att x)) : ℝ)) ∧
          (∀ i : Fin k,
            (2 * ((Finset.univ.filter (fun x : Fin n => x ∈ 𝓒.exc ∧ att x = i)).card : ℝ))
              ≤ (m : ℝ))) →
        (8 * ((⌈8 / c⌉₊ : ℕ) : ℝ) * (((𝓒.exc.card : ℕ) : ℝ)) *
          (((⌈1 / c⌉₊ : ℕ) : ℝ) + 5) ≤ (k : ℝ) * (m : ℝ)) →
        ∃ C : SimpleGraph (Fin n), C ≤ G ∧ IsHamiltonCycle' C

/-! ## The assembly: the two cluster-level inputs imply the engine -/

/-- The robust expansion of a graph is inherited when the robustness parameter is decreased. -/
theorem robustExpander_of_le {G : SimpleGraph (Fin n)} {ν ν' τ : ℝ} (hν : ν' ≤ ν)
    (h : RobustExpander G ν τ) : RobustExpander G ν' τ := by
  intro S h1 h2
  have h3 := h S h1 h2
  have hmono : robustNbrs G ν S ⊆ robustNbrs G ν' S := by
    intro x hx
    simp only [robustNbrs, Set.mem_ofPred_eq] at hx ⊢
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hc : ((robustNbrs G ν S).ncard : ℝ) ≤ ((robustNbrs G ν' S).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hmono
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hincl : ν' * (n : ℝ) ≤ ν * (n : ℝ) := by nlinarith
  linarith [h3, hc, hincl]

/-- **The assembly of the engine from its two cluster-level inputs.**

`ClusterReductionStatement` (regularity + the degree form + `robustR` + a cycle cover of the
reduced graph) and `FindCycleStatement` (the blow-up along that cycle cover) together imply the
chapter's engine `HamCycleStatement`.  There is no recursion: the reduction is applied once, at a
range parameter `τ` chosen small in terms of the minimum-degree fraction `α` (as the hierarchy
`4τ + c ≤ α/2` of the reduction requires — this is the `τ ≪ η` of Kühn–Osthus–Treglown), and its
output is fed directly to the blow-up.

The blow-up is invoked with the reduced graph's own robustness parameter `ν₁` (only its *lower*
bound `min (ν/8) (α/4) ≤ ν₁` is used, to see that `ν₁ ≥ ν/8`, which is what lets the blow-up be
called at the fixed value `ν/8` before `R` is known). -/
theorem hamCycleStatement_of_clusterReduction_and_findCycle
    (hRed : ClusterReductionStatement) (hFind : FindCycleStatement) : HamCycleStatement := by
  intro α hα
  -- the range parameter, chosen small in terms of `α`
  set τ : ℝ := min (α / 16) (1 / 8) with hτdef
  have hτpos : 0 < τ := lt_min (by linarith) (by norm_num)
  have hτ8 : τ ≤ 1 / 8 := min_le_right _ _
  have hτα : τ ≤ α / 16 := min_le_left _ _
  refine ⟨τ, hτpos, ?_⟩
  intro ν hν hντ
  have hνα : ν ≤ α := by linarith [hντ, hτα, hα]
  -- the expansion parameter of the reduced graph
  set c : ℝ := min (min (ν / 8) (α / 8)) (1 / 4) with hcdef
  have hcpos : 0 < c := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hc1 : c ≤ 1 / 4 := min_le_right _ _
  have hcν8 : c ≤ ν / 8 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcα8 : c ≤ α / 8 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hτc : 4 * τ + c ≤ α / 2 := by
    have h1 : 4 * τ ≤ α / 4 := by linarith
    have h2 : c ≤ τ / 8 := by
      refine le_trans hcν8 ?_
      rw [hτdef]; linarith
    linarith
  -- the reduction: first the cluster threshold `kF` of the blow-up, then its thresholds
  obtain ⟨εp, dp, hεppos, hεpdp, hεpratio, hdpc, hεpsmall, hRed'⟩ :=
    hRed α ν τ c hα hν hνα hντ hτ8 hτc hcpos hc1 hcν8 hcα8
  have hν8τ : ν / 8 ≤ 2 * τ := by linarith [hντ, hτpos]
  obtain ⟨kF, M₀, nF, hFind'⟩ :=
    hFind εp dp c (ν / 8) (2 * τ) hεppos hεpdp hdpc hc1 (by linarith) hν8τ hcν8
  obtain ⟨k₀, k₁, n₀, hRed''⟩ := hRed' kF M₀
  refine ⟨max n₀ nF, fun n hn G hG hdeg => ?_⟩
  obtain ⟨k, m, 𝓒, G', R, ν₁, hK, hK₁, hM₀, hm1, hν₁pos, hν₁min, hcν₁, hν₁τ, hm, hexc,
    hle, hind, hout, hpairs, hexcv, hCyc, hRob, hdegR, hexpR, hlossR⟩ :=
    hRed'' n (le_trans (le_max_left _ _) hn) G hG hdeg
  obtain ⟨σ, hσ⟩ := hCyc
  -- the minimum degree of `R` in the form the blow-up wants
  have h2c : ∀ i : Fin k, 2 * c * (k : ℝ) ≤ (Nat.card (R.neighborSet i) : ℝ) := by
    intro i
    have h := hdegR i
    have h2 : 2 * c ≤ α / 2 := by linarith [hcα8]
    have h3 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [h, h2, h3]
  -- the robustness of `R` at the fixed value `ν/8`
  have hν81 : ν / 8 ≤ ν₁ := by
    have h := hν₁min
    have h1 : ν / 8 ≤ min (ν / 8) (α / 4) := le_min le_rfl (by linarith [hα])
    linarith
  obtain ⟨C, hCG', hHam⟩ :=
    hFind' k hK n (le_trans (le_max_right _ _) hn) m hM₀ G' 𝓒 R σ
      hm hexc hind hout hpairs hσ (robustExpander_of_le hν81 hRob) h2c hexpR hexcv
  exact ⟨C, le_trans hCG' hle, hHam⟩

end

end Work.Deep.GKO