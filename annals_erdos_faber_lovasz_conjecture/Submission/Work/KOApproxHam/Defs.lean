import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.Combine
import Submission.Work.Deep.GKO.KOAssembly
import Submission.Work.Deep.GKO.KOReduction
import Submission.Work.Deep.GKO.RegVocab
import Submission.Work.Deep.GKO.ClusterEngine

/-!
# The approximate Hamilton decomposition: vocabulary

This is the chapter of mathematics needed for the **approximate Hamilton decomposition**
of Kühn–Osthus, *Hamilton decompositions of regular expanders* (arXiv:1202.6219 / JCTB 104
(2014)), Theorem 1.3 (due to Osthus–Staden, *Approximate Hamilton decompositions of robustly
expanding regular digraphs*, arXiv:1206.2810) — the second named tool of
`Work.Deep.GKO.ApproxHamDecompStatement`.

The theorem (translated to the undirected form used by this development) says: for every
`α > 0` there is `τ > 0` such that every `r`-regular robust `(ν,τ)`-expander with `r ≥ αn` and
`n` large contains `(1-η)r/2` edge-disjoint Hamilton cycles; equivalently, the edge set splits as
`G = G₁ ⊔ H₀` with `G₁` Hamilton-decomposable and `H₀` regular of degree at most `η r`.

## Contents

* `HamiltonCyclePacking` — `t` pairwise edge-disjoint Hamilton cycles in `G` (the "cycle
  packing" form of the theorem, which is the form in which the paper states it);
* `IsDecompSplit` — the splitting `G = G₁ ⊔ H₀`;
* `ApproxHamPackingStatement` — Theorem 1.3 in cycle-packing form;
* `BlowUpCert` — the certificate produced by the **clustering step** (Szemerédi's regularity
  lemma + the degree form): a cluster system, a pure subgraph `G' ≤ G` whose pairs are
  dense-uniform, the reduced graph `R` with a cycle cover, attached exceptional vertices, and the
  degree-loss bound for the non-exceptional vertices;
* `ClusteringStatement` — the clustering step as a named input (see `NOTES.md`: it is
  `Work.Deep.GKO.ClusterReductionStatement` plus the degree-loss clause);
* `BlowUpPackingStatement` — the **blow-up packing step** (the Osthus–Staden core): in the
  structure certified by `BlowUpCert`, `G` contains a cycle packing covering all but `η r` edges.

All definitions are stated in the vocabulary of `Work.Deep.GKO` (`IsHamiltonCycle'`,
`IsRegularOf`, `HasHamiltonDecomposition`, `RobustExpander`, `ClusterSystem`, `IsDenseUniform`,
`IsCycleCover`), so that the chapter composes with the rest of the GKO development.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KOApproxHam

open Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Cycle packings -/

/-- A **packing of `t` edge-disjoint Hamilton cycles** in `G`: subgraphs `C 0, …, C (t-1) ≤ G`,
each a Hamilton cycle (spanning and 2-regular), pairwise edge-disjoint.

This is the form in which Osthus–Staden state their theorem ("`G` contains at least `(1-η)r`
edge-disjoint Hamilton cycles"); the leftover of such a packing in an `r`-regular graph is
`(r - 2t)`-regular, which is why the packing form and the "regular leftover" form of
`Work.Deep.GKO.ApproxHamDecompStatement` are equivalent (`poset` of `Convert.lean`).  -/
def HamiltonCyclePacking (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  ∃ C : Fin t → SimpleGraph (Fin n),
    (∀ i, C i ≤ G) ∧ (∀ i, IsHamiltonCycle' (C i)) ∧
      (∀ i j, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet)

/-- The union of a family of graphs, used as the union of a cycle packing.  For a
`Finset.sup` over a `Fin t` index, this is the same as `⨆ i, C i`. -/
def packingUnion {t : ℕ} (C : Fin t → SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  Finset.univ.sup C

theorem packingUnion_def {t : ℕ} (C : Fin t → SimpleGraph (Fin n)) :
    packingUnion C = ⨆ i, C i := by
  rw [packingUnion, Finset.sup_eq_iSup]
  simp

theorem packingUnion_le {t : ℕ} {C : Fin t → SimpleGraph (Fin n)} {G : SimpleGraph (Fin n)}
    (h : ∀ i, C i ≤ G) : packingUnion C ≤ G := by
  rw [packingUnion_def]
  exact iSup_le h

/-- The edge set of the union of a packing is the union of the edge sets. -/
theorem edgeSet_packingUnion {t : ℕ} (C : Fin t → SimpleGraph (Fin n)) :
    (packingUnion C).edgeSet = ⋃ i : Fin t, (C i).edgeSet := by
  rw [packingUnion_def, SimpleGraph.edgeSet_iSup]

/-- A packing of `t` Hamilton cycles spans a `2t`-regular subgraph. -/
theorem isRegularOf_packingUnion {t : ℕ} {C : Fin t → SimpleGraph (Fin n)}
    (hcyc : ∀ i, IsHamiltonCycle' (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet) :
    IsRegularOf (packingUnion C) (2 * t) := by
  rw [packingUnion]
  have h := isRegularOf_finsetSup (Finset.univ : Finset (Fin t)) (C := C)
    (fun i _ j _ hij => hdisj i j hij) (fun i _ => (hcyc i).2)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-! ## Splitting a graph into a Hamilton-decomposable part and a regular leftover -/

/-- `G` **splits as `G₁ ⊔ H₀`**: both parts are subgraphs of `G`, they are edge-disjoint, and
their union is `G`. -/
def IsDecompSplit (G G₁ H₀ : SimpleGraph (Fin n)) : Prop :=
  G₁ ≤ G ∧ H₀ ≤ G ∧ Disjoint G₁.edgeSet H₀.edgeSet ∧ G₁ ⊔ H₀ = G

theorem IsDecompSplit.sdiff_eq {G G₁ H₀ : SimpleGraph (Fin n)} (h : IsDecompSplit G G₁ H₀) :
    G \ G₁ = H₀ := by
  obtain ⟨h₁, h₂, hdisj, hsup⟩ := h
  ext u v
  rw [SimpleGraph.sdiff_adj]
  constructor
  · rintro ⟨huv, hn₁⟩
    have := hsup ▸ huv
    rw [SimpleGraph.sup_adj] at this
    rcases this with h | h
    · exact absurd h hn₁
    · exact h
  · intro huv
    refine ⟨h₂ huv, ?_⟩
    intro h1
    exact (Set.disjoint_left.mp hdisj) ((SimpleGraph.mem_edgeSet G₁).mpr h1)
      ((SimpleGraph.mem_edgeSet H₀).mpr huv)

/-! ## The two formulations of Theorem 1.3 -/

/-- **Theorem 1.3 in cycle-packing form** (Osthus–Staden): for every `α > 0` there is `τ > 0`
such that for all `ν, η > 0` with `ν ≤ τ` there is `n₀` so that every `r`-regular robust
`(ν,τ)`-expander on `n ≥ n₀` vertices with `r ≥ αn` contains `t` edge-disjoint Hamilton cycles
with `r - 2t ≤ η r`. -/
def ApproxHamPackingStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧ ∀ ν η : ℝ, 0 < ν → 0 < η → ν ≤ τ → ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν τ → ∀ r : ℕ, IsRegularOf G r →
      α * (n : ℝ) ≤ (r : ℝ) → ∃ t : ℕ,
        HamiltonCyclePacking G t ∧ (r : ℝ) - 2 * (t : ℝ) ≤ η * (r : ℝ)

/-! ## The clustering certificate -/

/-- A permutation of the cluster indices is a **single cycle**: it acts transitively on `Fin k`.
This is how the certificate records that the reduced graph `R` has a Hamilton cycle `σ` (namely
`IsCycleCover R σ` together with transitivity), which is what makes the blow-up of the cycle
cover connected. -/
def IsSingleCyclePerm {k : ℕ} (σ : Fin k ≃ Fin k) : Prop := ∀ i j : Fin k, ∃ t : ℕ, (σ ^ t) i = j

/-- **The certificate of the clustering step.**  It bundles the output of Szemerédi's regularity
lemma + the degree form + the reduction to the density reduced graph, in the form in which the
blow-up packing step consumes it:

* `G` is `r`-regular (`hreg`); this is the hypothesis that ties the degree parameter `r` to the
  graph and without which the packing conclusion would be false;
* `G' ≤ G` is the *pure* subgraph (no edges inside a cluster, no edges between two clusters that
  are not adjacent in the reduced graph `R`);
* the clusters of `𝓒` all have size `m ≥ 1/εp` (large clusters), and the exceptional set has size
  at most `εp n`;
* adjacent clusters of `R` span `(εp,dp)`-dense-uniform pairs of `G'`;
* every exceptional vertex has at least `c m` neighbours in some cluster;
* every non-exceptional vertex keeps all but `γ n` of its neighbours: `r - γ n ≤ deg_{G'} x`;
* `R` is a robust expander of linear minimum degree and has the plain neighbourhood expansion,
  and `σ` is a *single* `k`-cycle of `R` (a Hamilton cycle of the reduced graph, recorded as a
  permutation: `IsCycleCover R σ` and `IsSingleCyclePerm σ`).

The numerical parameters `εp ≤ dp ≤ c ≤ 1/4` and `γ` are part of the statement (the caller
chooses them), which is why they are parameters of the structure. -/
structure BlowUpCert (n k m : ℕ) (εp dp c γ : ℝ) (G : SimpleGraph (Fin n)) (r : ℕ) where
  /-- the pure subgraph -/
  G' : SimpleGraph (Fin n)
  /-- the cluster system -/
  𝓒 : ClusterSystem n k
  /-- the reduced graph on the clusters -/
  R : SimpleGraph (Fin k)
  /-- the Hamilton cycle of the reduced graph, as a permutation -/
  σ : Fin k ≃ Fin k
  /-- its robustness parameters -/
  ν₁ : ℝ
  τ₁ : ℝ
  hk : 1 ≤ k
  /-- the clusters are large: `m ≥ 1/εp`.  This is what the regularity lemma gives when the
  partition is taken with `k` between the prescribed bounds and `n` large, and it is what the
  slicing step needs — with singleton clusters (`m = 1`) the blow-ups of cycle covers could only
  ever cover `2` edges per vertex, so no coverage statement could hold. -/
  hm : (1 : ℝ) / εp ≤ (m : ℝ)
  hreg : IsRegularOf G r
  hG'le : G' ≤ G
  hparts : ∀ i : Fin k, (𝓒.parts i).card = m
  hexc : ((𝓒.exc.card : ℕ) : ℝ) ≤ εp * (n : ℝ)
  hinner : ∀ i : Fin k, ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts i, ¬ G'.Adj x y
  hnonadj : ∀ i j : Fin k, i ≠ j → ¬ R.Adj i j →
    ∀ x ∈ 𝓒.parts i, ∀ y ∈ 𝓒.parts j, ¬ G'.Adj x y
  hpairs : ∀ i j : Fin k, i ≠ j → R.Adj i j →
    IsDenseUniform G' εp dp (𝓒.parts i) (𝓒.parts j)
  hatt : ∀ x ∈ 𝓒.exc, ∃ i : Fin k, c * (m : ℝ) ≤ (degIn G' x (𝓒.parts i) : ℝ)
  hloss : ∀ x : Fin n, x ∉ 𝓒.exc →
    (r : ℝ) - γ * (n : ℝ) ≤ (Nat.card (G'.neighborSet x) : ℝ)
  hν₁pos : 0 < ν₁
  hν₁τ₁ : ν₁ ≤ τ₁
  hτ₁4 : τ₁ ≤ 1 / 4
  hRrob : RobustExpander R ν₁ τ₁
  hRdeg : ∀ i : Fin k, 2 * c * (k : ℝ) ≤ (Nat.card (R.neighborSet i) : ℝ)
  hexpR : ∀ S : Finset (Fin k), c * (k : ℝ) ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - c) * (k : ℝ) →
    (S.card : ℝ) + c * (k : ℝ) ≤ ((nbrUnion R S).card : ℝ)
  hcov : IsCycleCover R σ
  /-- **The degree-loss margin** (the certificate-side hypothesis that excludes the *deeply
  deficient* vertices).  A vertex whose degree into **every** cluster is below `(dp - δ)m` has, by
  `hloss` and the fact that the `deg_R(i) ≥ 2ck` neighbouring pairs have density `≥ dp`,
  `δ < (γ + εp)·n/(2ck·m)`; such a vertex can neither be kept by the consistent-system refinement
  (whose window will have width `εp' = √(64(k+1)εp)` after the cleaning) nor attached.  All the
  refinement needs is therefore that the degree loss `γ` stays below the refined window's width:

    `γ·n ≤ 2ckm·εp'`,  `εp' := √(64(k+1)εp)`,

  which is the numeric form kept in `Submission/Work/KOApproxHam/windowAbs.lean`.  **Both** windows
  that `ConsistentSystem`/`windowAbs` ask for (the relative one and the absolute one) are *false*
  without this field; see the header of `consistentSystemPair.lean`.  A certificate satisfying it is
  produced by `ClusteringStatement` by taking the degree form's cluster-count parameter large
  enough (`k ≥ (γ/(16c))²/εp`), since the cluster size may be taken as small as `1/εp`. -/
  hγsmall : γ * (n : ℝ) ≤ 2 * c * (k : ℝ) * (m : ℝ) * Real.sqrt (64 * ((k : ℝ) + 1) * εp)

/-! ## The two named steps -/

/-- **The clustering step** (Szemerédi's regularity lemma + the degree form + Kühn–Osthus'
`robustR`).  For every `α, γ > 0`, every numerical hierarchy
`0 < εp ≤ dp ≤ c ≤ 1/4`, `dp + εp ≤ min γ (ν/8) (α/4)`, `0 < ν ≤ α`,
`ν ≤ τ ≤ 1/8`, `2τ + c ≤ α/2`, `c ≤ ν/8`, `c ≤ α/4`, and every lower bound `K` on the number of
clusters, every sufficiently large `r`-regular robust `(ν,τ)`-expander `G` with `r ≥ αn` admits a
clustering certificate `BlowUpCert n k m εp dp c γ G r` with `k ≥ K` and `m ≥ 1`.

The hypotheses are exactly the hierarchy under which the degree form of the regularity lemma with
the *prescribed* uniformity `εp` and density `dp` produces a partition whose density reduced graph
is a robust expander of linear minimum degree; a proof is a single application of
`Work.Deep.GKO.degreeForm` (proved) followed by the chapter's cluster-level tools
(`Work.Deep.GKO.denseOrEmptyPairs_of_pure`, `robustExpander_denseGraph`,
`plainExpansion_of_robustExpander`, `exists_cycleCover_of_robustExpander`,
`exists_cluster_degIn_ge`, `le_partSize_of_large_n`).  It is proved in this chapter as
`Work.KOApproxHam.clusteringStatement` (`ClusterStep.lean`). -/
def ClusteringStatement : Prop :=
  ∀ (α γ εp dp c ν τ : ℝ), 0 < α → 0 < γ →
    0 < εp → εp ≤ dp → dp ≤ c → c ≤ 1 / 4 →
    dp + εp ≤ γ → dp + εp ≤ ν / 8 → dp + εp ≤ α / 4 →
    0 < ν → ν ≤ α → ν ≤ τ → τ ≤ 1 / 8 → 2 * τ + c ≤ α / 2 →
    c ≤ ν / 8 → c ≤ α / 4 →
    ∀ K : ℕ, 1 ≤ K → ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν τ → ∀ r : ℕ, IsRegularOf G r →
        α * (n : ℝ) ≤ (r : ℝ) →
        ∃ k m : ℕ, K ≤ k ∧ 1 ≤ m ∧ (1 : ℝ) / εp ^ 3 ≤ (m : ℝ) ∧
          Nonempty (BlowUpCert n k m εp dp c γ G r)

/-- **The blow-up packing step** (the Osthus–Staden core, their §5–§7).  Given the numerical
hierarchy `0 < εp ≤ dp ≤ c ≤ 1/4`, a loss parameter `γ > 0` with `γ ≤ η/4`, a tolerance `η > 0`
and the absolute smallness relation `4γn ≤ ηr`, there are bounds `K`, `n₀` such that for every
`k ≥ K`, `n ≥ n₀`, `m ≥ 1`, every `r`-regular graph `G` on `n` vertices carrying a clustering
certificate with `k` clusters of size `m`, the graph `G` contains `t` edge-disjoint Hamilton
cycles with `r - 2t ≤ η r`.

In Osthus–Staden's proof this is the long construction: the reduced multigraph is regularised by
max-flow/min-cut and sliced into 1-factors (`§5`), the slices are completed with the reserved
sparse subgraphs `H₀, H₁, H₂` (bridge vertices, the exceptional sets `§6`), each slice is reduced
to a regular spanning subgraph which is 1-factorized and whose 1-factors are merged into Hamilton
cycles using the blown-up cycles of the reduced graph (`§7`, Lemma `trick`).  See `NOTES.md`
for the finer decomposition into the *slicing* step and the *merging* step. -/
def BlowUpPackingStatement : Prop :=
  ∀ (εp dp c γ η : ℝ), 0 < εp → εp ≤ dp → εp ≤ dp * dp / 100 → dp ≤ c → c ≤ 2 * dp →
    c ≤ 1 / 4 →
    0 < γ → γ ≤ η / 4 → 0 < η →
    ∃ K n₀ : ℕ, 1 ≤ K ∧ 1 ≤ n₀ ∧ ∀ k ≥ K, ∀ n ≥ n₀, ∀ m : ℕ, 1 ≤ m →
      (1 : ℝ) / εp ^ 3 ≤ (m : ℝ) →
      ∀ (r : ℕ) (G : SimpleGraph (Fin n)) (Cert : BlowUpCert n k m εp dp c γ G r),
        4 * γ * (n : ℝ) ≤ η * (r : ℝ) →
        ∃ t : ℕ, HamiltonCyclePacking G t ∧ (r : ℝ) - 2 * (t : ℝ) ≤ η * (r : ℝ)

end

end Work.KOApproxHam
