import Submission.EFL.Basic
import Submission.EFL.LineGraph
import Submission.EFL.Reformulation
import Submission.EFL.BigEdges

/-!
# Roadmap for a complete proof of `theorem_1_1`

The target theorem (Erdős–Faber–Lovász for large `n`) is Theorem 1.1 of
D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, D. Osthus, *A proof of the
Erdős–Faber–Lovász conjecture*, Annals of Math. 198 (2) (2023)
(arXiv:2101.04698v3).  Its proof is long and deep; this file records the
state of the formalisation and maps the remaining work to the paper.

## What is already formalised and machine-checked (in `Submission/EFL`)

* `Basic.lean` — API for the exact `ChallengeDeps` definitions
  (`Hypergraph`, `Coloring`, `IsLinear`, `chromaticIndex`):
  `chromaticIndex ≤ n ↔ Colorable n` for hypergraphs on finite vertex types,
  monotonicity of the chromatic index, colour-preserving operations
  (extension of colours, restriction to sub-hypergraphs, recolouring).

* `LineGraph.lean` — a hypergraph colouring is the same thing as a colouring
  of the line graph `lineGraph 𝓗` (vertices = edges, adjacent when distinct
  and intersecting).  Hence `chromaticIndex 𝓗 ≤ n ↔ (lineGraph 𝓗).Colorable n`
  and Mathlib's graph-chromatic-number API is applicable.

* `Reformulation.lean` — the theorem statement in its equivalent forms:
  `eflStatement` (`∀ᶠ n in atTop, …`), `eflStatementThreshold`
  (`∃ N, ∀ n ≥ N, …`) and the line-graph form `eflStatementLineGraph`,
  all provably equivalent (`eflStatement_iff_threshold` etc.).

* `BigEdges.lean` — the first reduction of the paper: it suffices to prove the
  theorem for linear hypergraphs whose edges all have ≥ 2 vertices
  (`eflStatement_of_bigEdges`).  Includes the elementary linear facts used:
  distinct edges share at most one vertex; an edge through two vertices is
  unique; at most `n - 1` edges of size ≥ 2 pass through a fixed vertex; a
  colouring of the large edges extends to the singleton edges (each vertex
  misses at least one colour).

* `Matching.lean` — the paper's *working definition* of a colouring (used in
  §12): a family of edges is a *matching* when its members are pairwise
  vertex-disjoint (`IsMatching`); the colour classes of a colouring are
  matchings, and conversely `𝓗.Colorable n ↔ HasMatchingDecomposition n 𝓗`
  ("`n` pairwise edge-disjoint matchings containing all the edges");
  a matching is exactly an independent set of the line graph
  (`isMatching_iff_isIndepSet`).

* `Counting.lean` — pair double-counting in a linear hypergraph on `n`
  vertices: `∑_e |e|·(|e|−1) ≤ n(n−1)` (`sum_edgeSize_mul_sub_le`, via the
  fact that an unordered pair of vertices lies in at most one edge); as a
  consequence at most `n(n−1)/(s(s−1))` edges have size at least `s ≥ 2`
  (`card_edges_size_ge_le`).  This is the engine behind every estimate on
  the number of FPP-extremal / huge edges.

* `NeighbourSum.lean` — the §6.2 neighbour-sum engine: for a linear
  hypergraph and an edge `e`, `∑_{f ∈ N(e)} (|f|−1) ≤ |e|·(n−|e|)`
  (`sum_neighbour_size_sub_le` and its real cast `sum_neighbour_real_le`,
  first lines of the proof of Prop `fwdnbr`), with the cross-pair
  machinery and the subclass bounds `card_neighbour_family_mul_le` /
  `card_neighbour_family_le` used by the reordering lemma's counting.

* `EdgeSize.lean` — the paper's edge classes (Definition `def:edgesize`):
  `small`/`med`/`large` by size thresholds `r₁ ≤ r₀`, plus `FPP-extremal`
  and `huge`; each is a sub-hypergraph preserving linearity and the three
  size classes cover the edge set (`union_small_medium_large`).

* `FewLargeColourClasses.lean` — **the first theorem-level layer of the
  proof of Theorem 6.7**, Proposition `few-large-colour-classes`(i) of §7:
  `familyVolume`/`familyNatVolume`/`sumEdgeSizes`, the volume lower bound
  `familyNatVolume_ge_mul_sum` (edges ≥ r+1 ⇒ vol ≥ r·(Σ|e|)/(n(n−1))),
  `familyVolume_le_one`, and the counting bound
  `fewLargeColourClasses_bound` (pairwise edge-disjoint matchings, each
  covering ≥ αn vertices, edges of size ≥ r+1: `t·αr ≤ n−1`) with the
  paper's division form `fewLargeColourClasses_le` (`t ≤ n/(αr)`).

* `ColourClassCounting.lean` — the wrapper layer: `EdgeSetFamily` turns any
  set of edges / colour class into a finite family of vertex sets; matchings
  lift to matching families (`IsMatchingFamily_of_IsMatching`), colour-class
  vertex coverage agrees with the family count
  (`classVertexCount_eq_FamilyVertexCount`), and the paper's
  `few-large-colour-classes`(i) is derived in colour-class language:
  `fewLargeColourClasses_of_colorClasses` and `card_bigColourClasses_le`
  (at most `n/(αr)` colours whose class covers ≥ αn vertices, given every
  edge of the hypergraph has size ≥ r+1).

* `ColourClassSplitting.lean` — the margin splitting engine for step (b) of
  `few-large-colour-classes`(ii): integer greedy chunking by vertex coverage
  at the threshold `A = ⌈αn/2⌉` (`exists_prefix_*`, `exists_chunk_intervals`,
  `chunk_matching_by_coverage`), the partition of a colour class's edge list
  into singletons (big edges) + consecutive chunks + one leftover
  (`colour_edges_split_witness`, margin form
  `colour_edges_split_witness_piece_PieceOKMargin`), the lifting to colour
  classes (`SplitColourClassMarginStatement`, `splitColourClassMargin`, and
  the exact-once form `splitColourClass_exactlyOnce`), the threshold bounds
  (`SplitThreshold_lower/upper`), and the *margin-tolerant* piece predicate
  `PieceOKMargin` (coverage ≥ αn/2; `< αn + 1` unless a singleton).
  NB: the old def `SplitColourClassStatement` in this file (pieces each
  covering ∈ [αn/2, αn], count ≤ 2/α) is **false** in corner cases (e.g. a
  class of three disjoint `0.4αn`-edges, or the greedy leftover below
  `αn/2`); it is kept only as documentation.

* `ColourClassSplitHonest.lean` — **the honest colour-class splitting
  theorem** (`splitColourClassHonest` / `SplitColourClassHonest`), the
  corrected form of Prop 6.8's partition claim: every colour class (no
  coverage hypothesis needed) splits into at most `2/α + 1` pairwise
  edge-disjoint matching pieces, each a subfamily of the class and either a
  single edge or covering `< αn + 1` vertices, with every edge of the class
  in exactly one piece (one exceptional "leftover" piece may cover
  `< αn/2`).  This is the piece-count input to the α-bounded recolouring
  step of `few-large-colour-classes`(ii): applying the split at parameter
  `α/2` gives pieces covering `≤ αn` vertices for `n ≥ 2/α`, so the `+1`
  margin is absorbed exactly as the hierarchy allows.

* `AlphaBoundedColouring.lean` — **the honest α-bounded recolouring
  theorem** (`alpha_bounded_recolour`), i.e. Prop 6.8(ii)
  (`few-large-colour-classes`(ii)): given a proper edge-colouring `φ` of a
  linear hypergraph with all edges of size `≥ r+1` using the colours of
  `C`, an `β`-bounded proper edge-colouring exists using at most
  `|C| + (2/(β/2)+1)·n/((β/2)r)` colours.  The big colour classes (covering
  `> βn/2`) are split by `splitColourClassHonest` at the halved parameter
  `β/2`, each class into ≤ `2/(β/2)+1` pieces that are single edges or cover
  `≤ βn` vertices (`SplitPieceOK_half_strict`); the remaining classes are
  kept.  Machinery: host-independent `Coloring.AlphaBounded` (agreeing with
  `classVertexCount` via `classVertexCount_eq_FamilyVertexCount`), and the
  colouring-from-family construction `colouringOfFamilies_fin_AlphaBounded`
  (a finite family of pairwise disjoint matching families covering the
  edges yields a colouring whose classes are exactly the members).

* `GreedyListColouring.lean` — **Prop 6.9 (greedy list-colouring)
  PROVED** with the ordering vocabulary (rank `ord : 𝓗 ≃ Fin k`,
  `precedingDegree 𝓗 ord e` = `d⪯(e)`), the full extension engine
  (huge successor ⇒ fresh colour, class a singleton; small successor ⇒
  colour outside `C₁ ∪ C₂`, with `|C₁| ≤ d⪯(f)` and
  `|C₂| ≤ 2n/(α₂(r−1))`), the maximal-prefix argument
  (`greedy_colouring_hugeFirst`), the huge-first reordering of an
  arbitrary ordering with `fwddeg' ≤ fwddeg + #big`
  (`exists_hugeFirst_reorder`, `fwddeg_le_of_reorder`), and the assembly
  `prop69_colouring` / `prop69Instance` (`Prop69Instance`): linear, all
  edges `≥ r`, any ordering, lists `|C(e)| ≥ d⪯(e) + α₁n` ⇒ an
  `α₂`-bounded proper colouring with `φ(e) ∈ C(e)`, under the margins
  `2n/(α₂(r−1)) < α₁n/4` and `#big < α₁n/2`.  (The margins are supplied
  by the hierarchy `0 < 1/n₀ ≪ 1/r ≪ α₁, α₂` at assembly level.)

* `OrderConcat.lean` — `concatOrdering`: given a partition of the edges of
  `𝓗` into `P`, `Q` and orderings of each part, the concatenated ordering
  `𝓗 ≃ Fin (kP + kQ)` in which every edge of `P` precedes every edge of `Q`
  (with the rank/comparison lemmas `concatOrdering_apply_of_mem`,
  `concatOrdering_lt_of_mem_of_notMem`, `concatOrdering_le_iff_of_mem`) —
  the tool with which the paper's Figure 3 assembles the orderings obtained
  from three applications of the reordering lemma.

* `ClassicalBounds.lean` — **the classical bounds, proved unconditionally**:
  `chromaticIndex_le_two_mul_add_one` (`χ′ ≤ 2n+1` for every linear
  hypergraph on `n` vertices) and `colorable_of_min_edgeSize`
  (`χ′ ≤ (1 + 1/(r₁−1))n + 1` when every edge has size `≥ r₁ ≥ 2`), via
  `colorable_of_precedingDegree_le` (greedy colouring along an ordering in
  which every edge has at most `k−1` preceding neighbours) and the
  size-order forward-degree bounds `precedingDegree_sizeOrder_le`
  (`d⪯(e) ≤ n + n/(|e|−1)` for `|e| ≥ 2`) and
  `precedingDegree_sizeOrder_le_le_one` (`d⪯(e) ≤ |e|(n−|e|)` for `|e| ≤ 1`).

* `LocallySparse.lean` — **the reduction of §6.2's locally-sparse-graph
  colouring corollaries to the two deep inputs, with all the counting
  proved**: the input statements `MolloyReedStatement` (paper Thm 6.4) and
  `AKSStatement` (paper Thm 6.6) on `SimpleGraph`; `nbrEdges G v` (=
  `e(G[N(v)])`); the line-graph counting `card_neighbourEdges_le`
  (`Δ(L) ≤ |e|(n−|e|)/(r−1)`) and `card_commonNeighbours_le`
  (`|N(e)∩N(f)| ≤ n/(r−1) + |e||f|` for intersecting `e ≠ f`, both edges of
  size `≥ r`); the bridge to the line graph
  (`lineGraph_neighborFinset`, `card_neighborSet_lineGraph`,
  `sum_degree_lineGraph_le`, `nbrEdges_lineGraph_le`,
  `lineGraph_maxDegree_le`); and the two corollaries **proved** from the
  deep inputs: `corollary_6_5` (`χ′(H) ≤ (1−ζ/500)n` for edge sizes in
  `[r, (1+α)r]`, `r ≤ (1−ζ)√n`) and `corollary_6_7` (`χ′(H) ≤ εn` for edge
  sizes in `[1/η, η√n]` within a factor `1/α`), with the paper's hierarchies
  isolated in the margin structures `Corollary65Margins`/`Corollary67Margins`.

* `LargeEdge.lean` — **Theorem 6.7 (`large-edge-thm`) of the paper, stated
  precisely on the exact definitions** (the main milestone of the remaining
  proof): colour-class coverage (`Coloring.classVertexCount`), the
  non-extremal alternative `LargeEdgeNonExtremal` (colour class (i)–(iii)),
  the extremal alternative `LargeEdgeExtremal` (FPP-extremal set of volume
  ≥ 1−δ plus (i)–(iii)), hypergraph `volume`, the volume bound
  `volume_le_one_of_linear` for linear hypergraphs (via the pair counting),
  the per-instance statement `LargeEdgeInstance`, and the hierarchy-level
  `LargeEdgeThmStatement`.  The module header records the proof
  decomposition of Theorem 6.7 (reordering lemma, few-large-colour-classes,
  greedy colouring, Molloy–Reed / AKS local sparsity, the extremal regime of
  §6, and the §7 assembly).

## Where the proof stands

Everything through the paper's opening reduction and vocabulary is machine
checked (see the list above).  The mathematical heart of the proof — the
*deep theorems* below, their many supporting lemmas (absorption, reservoirs,
nibbles) and the assembly in §12 — is not yet formalised; the modules above
give the definitions (`HasMatchingDecomposition`, edge-size classes, pair
counts) in which those results must be stated and the bridge
(`colorable_iff_hasMatchingDecomposition`) by which the final decomposition
yields `theorem_1_1`.

### Milestones already reached (machine checked)

* **The Reordering Lemma (Lemma 6.2)**: fully proved in `Reordering.lean`
  (Blocks I–VI, the minimality dichotomy, the volume bound `WVolume`), with
  the two applications of `fwdnbr_inequality2` (`blockV_app2`) and the
  `t`-arithmetic; the volume witness records `eStar ∈ W`.
* **Proposition 6.9 (greedy list-colouring)**: `GreedyListColouring.lean`
  (`Prop69Instance`, `prop69Instance`).
* **Proposition 6.8 (few large colour classes)**: `FewLargeColourClasses.lean`
  (`fewLargeColourClasses_bound`, `fewLargeColourClasses_le`), plus the
  split/recolouring machinery (`ColourClassSplitting.lean`,
  `ColourClassSplitHonest.lean`, `AlphaBoundedColouring.lean`).
* **Corollaries 6.5 and 6.7** (locally sparse colouring, reduced to the two
  deep inputs `MolloyReedStatement` and `AKSStatement`): `LocallySparse.lean`.
* **Theorem 1.3 (weak stability)**: **PROVED** in `WeakStabilityMain.lean`
  as `weakStability_of_deep (hK : KahnStatement) (hAKS : AKSStatement) (ε)
  (hε0) : WeakStabilityInstance ε` — i.e. from Kahn's theorem (4.6) and
  Alon–Krivelevich–Sudakov (6.6) only.  (Not on the critical path of
  Theorem 1.1: the paper states explicitly that Theorems 1.2 and 1.3 are
  not used in the proof of Theorem 1.1.)
* **The whole §5 chain (Lemma 5.1) ported to minimal imports**:
  `Submission/EFL/Nearfull/` — the commons files begin with `import Mathlib`
  and are unimportable here, so `linear_nearfull_colouring` (and its five
  supporting files) were re-elaborated against minimal imports (found with
  Mathlib's `#min_imports in`); `Submission.lean` now imports
  `Submission.EFL.Nearfull.LinearNearfullColouring`.
* **Theorem 6.1's case split**: `LargeEdgeCases.lean` — `case1_of_blocks`
  (Case 1) and `largeEdge_of_blocks` (Cases 1 + 2.1 + Case 2.2 as the single
  outstanding hypothesis `h22`).
* **THE CASE ANALYSIS OF THEOREM 6.1 IS COMPLETE**
  (`LargeEdgeCase22Main.largeEdge_of_blocks_full`).  Case 2.2 of Figure 3 is
  proved end-to-end: the size bound `|e| ≤ δn/2` (`case22_noBig`), the two
  Proposition 6.9 firings with their list bounds
  (`case22_fwddeg_good₂/₁`, `case22_list_bound₂/₃`), the colour set
  `C_med ⊆ univ ∖ C_huge` (`case22_exists_Cmed`), the glue by
  `coloringUnionCross` and the class estimates
  (`case22_colouring`/`case22_extremal`).  The fourth sub-case
  (`W₂ ≠ ∅`, `r₃ ≥ (1−δ)√n`, `r₃ > √(n/(1−4σ))`) supplies the paper's
  `eqn:d3-upper-bound`: the pair count gives `e(𝓗₂^left) ≤ (1−3σ)n`
  (`case22_left_card_le`), so the App-2 ordering is *good*
  (`case22_good_ordering`) and Case 1 applies
  (`case1_of_blocks_of_good`).  `r₂ ≥ γ₂^{10} r₃`
  (`r₂_ge_r₃_of_blocks`) is likewise *proved*, from the intersection
  `W₁ ∩ W₂ ≠ ∅` of the two Reordering-Lemma volume sets — which is why
  `BlocksOK` now records the App-1 volume set `W₁` and its `(W1)`-properties.
  The only remaining hypotheses are the numeric margins of the hierarchy.
* **The parameter hierarchy of Theorem 6.1 in progress**
  (`LargeEdgeHierarchy.lean`): the counting bound `bigFinset_card_le`, the
  thresholds `δThr`/`σThr`/`γ₁Thr`/`βThr`/`ζc`/`R₀Thr`/`R₁Thr`/`N₀Thr` with
  their properties, all the parameter-only margins
  (`volBound_three_sigma_ge`, `sizeFactor_three_sigma_le`,
  `app1_volBound_gt`, `δThr_le_app3`, …), all the `n`-margin lemmas
  (`margin_sqrt`, `margin_huge`, `margin_bigFinset`, …), the colour-budget
  margins (`margin_room1` … `margin_C1K`), and the medium-edge colouring
  `medEdges_colouring_of_kahn` (Proposition 6.10 from Kahn's theorem).  The
  final assembly `largeEdgeThmStatement_of_deep` is in progress; the
  elaborated draft is in `Submission/EFL/LargeEdgeHierarchyWIP.txt`.
* **Vizing's theorem** in the shared commons
  (`Commons.Combinatorics.SimpleGraph.vizing`), as are Lemma 5.1
  (`Commons.Combinatorics.Hypergraph.linear_nearfull_colouring`).
* **The Fig. 3 firings**: `app1_firing` (`LargeEdgeSetup.lean`),
  `app2_firing`, `app3_firing` (`Reordering.lean`), with the numeric bounds
  `app1_sizeFactor_le`, `app1_volBound_ge`, and the App-3 collapse
  `app3_volume_collapse`/`app3_closing`/`app3_good`.

### THEOREM 6.1 (`large-edge-thm`) IS PROVED (this session)

**STATUS: COMPLETE modulo the deep inputs.**  The module
`Submission/EFL/LargeEdgeThm.lean` contains

```
theorem largeEdgeThmStatement_of_deep (hMR : MolloyReedStatement)
    (hK : KahnStatement) : LargeEdgeThmStatement
```

machine-checked and axiom-clean (`propext, Classical.choice, Quot.sound`).
It is built from two layers:

* **`largeEdgeInstance_of_thresholds`** (the per-instance layer): for fixed
  parameters with `δ ≤ δThr γ₂`, `σ ≤ σThr δ`, `γ₁ ≤ γ₁Thr σ`,
  `β ≤ βThr γ₁`, `R₁Full ≤ r₁`, `R₀Full ≤ r₀`, `N₀Full ≤ n`, every linear
  hypergraph on `Fin n` with all edge sizes `> r₁` is
  `LargeEdgeNonExtremal ∨ LargeEdgeExtremal`.  It fires
  `exists_largeEdgeBlocks` (App 1 + App 2), colours the medium edges with
  `medEdges_colouring_of_kahn` (Proposition 6.10 from Kahn), discharges all
  ~74 numeric hypotheses of `largeEdge_of_blocks_full` with the `margin_*`
  lemmas, and applies the case analysis.
* **`largeEdgeThmStatement_of_deep`** (the threshold layer): destructures
  Molloy–Reed (as `Δ₀, C, m` + the polynomial threshold bound) and Kahn,
  obtains Lemma 5.1's `n₀` from `nearfullColouring_exists`, reduces `γ₂` to
  `γ₂' := min γ₂ (1/4000)`, and chooses `δ₀, σ₀, γ₁₀, β₀, R₁, R₀, N₀` in
  the order of the paper's `≪`-hierarchy.

New numeric tools proved in the same module: `margin_hfac`
(`(W1)`'s size-factor estimate), `margin_m22₃`, `margin_bigFinset_ratio`
(the `bigFinset` count at an arbitrary ratio `c`, via `margin_bigFinset`
with `σ := 2c`), `margin_bigFinset_ratio`-fed `hb22₂`/`h69b`/`h69bσ`/`hbig`,
`kahn_two` (Kahn at `α = 1`, the form consumed by Prop 6.10),
`γ₁Thr_le_quarter`, `γ₁Thr_le_half`, `σThr_le_inv_million`,
`δThr_le_self`, `βThr_le`, `βThr_le_two_thirds`, and the thresholds
`R₁Full`, `R₀Full`, `N₀Full`.

Earlier milestones of §6 (kept below for the record).

1. **Proposition 6.10 (`prop:med-edges`) — DONE** (`MedEdges.lean`):
   `medEdges_colouring_of_chi` gives the `γ`-bounded colouring of `𝓗_med`
   with at most `γn` colours from the chromatic-index input
   `χ' ≤ 4n/r₁ + 1`, and `colorable_of_kahn_sizes` derives that input from
   `KahnStatement` using the new degree bound `maxDegree_le_div`
   (`Δ(𝓗) ≤ n/(r₁−1)` for linear `𝓗` with all edges of size ≥ r₁; from
   `degree_mul_le`).  The thresholds used are `γ ≤ 1/2`, `2 ≤ γn`,
   `32/γ³ + 8/γ² + 8/γ ≤ r₁`, `D₀ ≤ n/(r₁−1)`.
2. The Fig. 3 decomposition: fire App 1 on `𝓗' = 𝓗 ∖ 𝓗_huge` (`app1_firing`,
   `LargeEdgeSetup.lean`), App 2 on `𝓗₁^left` (`app2_firing`), App 3 on
   `𝓗₃` (`app3_firing`, collapsed to a good ordering by `app3_good`), build
   the combined ordering `⪯`, and prove the partition
   `𝓗 = 𝓗₂^left ⊔ 𝓗₂^good ⊔ 𝓗₁^good` with `𝓗₂^left = 𝓗₃ ⊔ W₂` and the
   forward-degree bounds (a)–(f) of the paper.  The volume bounds to carry
   are `app1_sizeFactor_le` (`(W₁1)`), `app1_volBound_ge` (`(W₁2)`),
   `app2_volume_bound` (`(W₂2)`), and the App-3 collapse
   (`app3_volume_collapse`/`app3_closing`/`app3_good`).
3. **Case 1 (`⪯₂` good) — the Prop 6.9 + 6.10 assembly is DONE**
   (`LargeEdgeCase1.lean`): `largeEdge_case1` proves
   `LargeEdgeNonExtremal` from a *good ordering of the large edges* (all
   preceding degrees `≤ (1−2σ)n`) plus the Prop 6.10 colouring of the
   medium edges, using the colour-union glue of `ColourUnion.lean`
   (`coloringUnionOfCover`) and verifying (6.1:a)(i)–(iii).  `largeEdges`
   and `medEdges` (real-threshold versions), `edgeMedium_iff_mem_medEdges`,
   `cover_large_med_edges`, `disjoint_large_med_edges`, and the
   colour-class vertex-count lemmas live there too.  What is still missing
   for Case 1 is only the *production of the good ordering* from the
   Figure-3 firings (see below).
4. **One Reordering-Lemma application split into the Figure-3 shape — DONE**
   (`ReorderingSplit.lean`): `reordering_split` turns one firing of the
   Reordering Lemma on a subfamily `𝓖 ⊆ 𝓗` into an ordering `ord : 𝓖 ≃ Fin k`
   plus a partition `𝓖 = Good ⊔ Left` (with `Left` an initial segment of
   `ord`), a threshold `r₂` bounding the sizes on `Left` from below, and a
   finset `W ⊆ Left` with `W = ∅ → Left = ∅`, `vol(W) ≥ volBound τ K`
   unless `W = ∅`, and `|e| ≤ sizeFactor τ K · r₂` on `W`.  It also provides
   `app3_good_of_disjoint` (the App-3 collapse in the general
   disjoint-subfamilies form used for `𝓗₃ = (𝓗₁^left ∖ W₂) ∪ 𝓗_huge`) and
   `natCard_interFiber_le_add` (splitting a neighbourhood count over a
   disjoint cover).  The three Figure-3 applications are then
   `reordering_split` at `(app1tau γ₂, app1K γ₂)` on `nonHuge 𝓗 β`,
   at `(3σ, 1)` on `𝓗₁^left`, and `app3_good_of_disjoint` on `𝓗₃`.
5. **Remaining for Theorem 6.1** (in dependency order):
   (a) **DONE** (`Fig3Case1.lean`): `app1_split` (App 1 with the numeric
       bounds `(W₁1)`/`(W₁2)` substituted) and the huge-edge counts
       `card_huge_le` / `natCard_hugeEdges_le` (`≤ 32/β²`; the pair-counting
       substitute for the paper's (2.2)).  Still missing: an `app2_margins`
       lemma producing `ReorderingMargins r₁ (3σ) 1` from `r₁ ≥ R(σ)`,
       `σ ≪ 1` (the analogue of `app1_margins`; the shape is a finite list
       of elementary inequalities in `r₁ = (r₁:ℝ)`).
   (b) **Case 1 is DONE modulo the final case split**
       (`Fig3Case1.lean`): `exists_goodOrdering_of_app1_app2` +
       `largeEdge_nonExtremal_of_app1_app2` turn "the App-2 firing is good"
       into `LargeEdgeNonExtremal`.  To close Theorem 6.1's proof, fire
       App 1 (`app1_split`) and App 2 (`reordering_split` at `(3σ,1)` on
       `𝓗₁^left`) once, then split on `W₂ = ∅`:
       * `W₂ = ∅` ⇒ `𝓗₂^left = ∅`, `𝓗₂^good = 𝓗₁^left`, and the two lemmas
         above give `LargeEdgeNonExtremal` (needs `hseg`/`hdeg`/`hdeg₂` from
         the two splits, whose statements already return them);
       * `W₂ ≠ ∅` ⇒ Case 2 (below), where `𝓗₃ := (𝓗₁^left ∖ W₂) ∪ 𝓗_huge`
         gets a good ordering from `app3_good_of_disjoint`
         (`ReorderingSplit.lean`) using the App-2 volume bound
         `1−δ³ ≤ volBound (3σ) 1` and `δ ≤ volBound app3tau app3K`.
   (c) **Case 2.1** (`r₃ < (1−δ)√n`): `LargeEdgeNonExtremal`.  Progress
       (this session):
       * `LargeEdgeBlocks.lean`: **the App-1/App-2 block decomposition**
         (`BlocksOK` + `exists_largeEdgeBlocks`) — the two splits, the
         thresholds `r₂, r₃` (`hr₂`/`hr₃`, with `hW₂thr` recording that `r₃`
         is an edge size in the volume case), the volume set `W₂`
         (`hW₂vol`, `hW₂size`, `hW₂size_le`), the residual family
         `𝓗₃ = 𝓗_huge ∪ (𝓗₂^left ∖ W₂)` (`hH₃sub`, `hH₃huge`, `hH₃mem`,
         `hH₃W₂disj`) and the partition
         `𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good` (`hcover`, the four
         disjointness fields).  `reordering_split` gained the conjunct
         `(W = ∅ ∧ r₂ = r₁) ∨ ∃ e ∈ W, |e| = r₂` (whence `hr₂`/`hr₃`).
       * `ColourCombine2.lean`: **the Case-2 colouring toolkit** —
         `Coloring.map` / `exists_coloring_usesColourSet` (move a colouring
         into a prescribed colour set, preserving `AlphaBounded`),
         `coloringUnionCross` (combine two colourings of a cover under a
         *cross-condition*, colour sets not required disjoint),
         `classVertexCount_coloringUnionCross_le`,
         `classVertexCount_le_of_alphaBounded`, and the assembly
         `largeEdge_nonExtremal_of_largeColouring` — the non-extremal
         alternative from a large-edge colouring whose huge classes are
         singletons (`hsingL`) and whose other classes cover `≤ βn`
         (`hsmallL`).  This is the glue the Case-2 colourings feed into.
       * `LargeEdgeCase2.lean`: `case2Left`/`case2Right` (`𝓗₂^left∖𝓗_med`
         and `(𝓗₂^good∪𝓗₁^good)∖𝓗_med`), `case2_parts` (they partition
         `𝓗_large`, sizes `≥ r₀`, the right block lies in `𝓗 ∖ 𝓗_huge`),
         `hugeColourSet`/`card_hugeColours_le` (the set `C_huge` of colours
         assigned to huge edges has `≤ 32/β²` elements), and
         `sparse_colouring_usesColourSet` — Claim
         `claim:sparse-colouring` (Corollary 6.5 + Proposition 6.8(ii)) in
         the prescribed-colour-set form.
       * **App 3 fired on `𝓗₃`** (`case2_H3_goodOrdering`): in the volume
         case `𝓗₃` gets `GoodOrdering app3tau` (via
         `app3_goodOrdering_of_volume` + the App-2 volume bound), and by
         `exists_restricted_ordering` so does `𝓗₃∖𝓗_med`, with forward
         degree `≤ n/2000`.  Hence `case2_H3_colouring`: `𝓗₃∖𝓗_med` has a
         `β/5`-bounded colouring using *any* prescribed colour set of size
         `≥ n/1500` (Prop 6.9 with `α₁ = 1/6000`, `α₂ = β/5`, lists
         `n/1500 = n/2000 + n/6000`) — Claim `claim:before-W-colouring`.
       * **Claim `claim:sparse-colouring`** (`case2_W2_sparse`):
         `W₂∖𝓗_med` has a `β/5`-bounded colouring using any prescribed
         colour set of size `≥ (1−ζ/1000)n` (sizes `∈ [r₃, B₀]` from
         `BlocksOK`, Corollary 6.5 + Prop 6.8(ii) via
         `sparse_colouring_usesColourSet`).
       * `case2_cover_parts`: `(W₂∖𝓗_med) ∪ (𝓗₃∖𝓗_med) = 𝓗₂^left∖𝓗_med`,
         so the two colourings above combine (`coloringUnionOfCover` on
         disjoint prescribed colour sets) into `φ₁` with
         `|C₁| ≤ (1−2σ)n`.
       * **`φ₁` DONE** (`case2_colouring_left`): the two claims combine by
         `coloringUnionOfCover` on disjoint prescribed colour sets
         (`C' ∪ C''`, chosen as subsets of `Fin n ∖ Cmed` with card
         `⌈(1−ζ/1000)n⌉` and `⌈n/1500⌉`), giving a `β/5`-bounded colouring
         of `𝓗₂^left ∖ 𝓗_med` with `|C₁| ≤ (1−2σ)n` and `C₁ ∩ Cmed = ∅`.
         The `AlphaBounded` transport uses the new class-transfer lemmas
         `ncard_colorClass_coloringUnionOfCover_left/right`
         (`(union.colorClass c).ncard = (φ₁.colorClass c).ncard` for
         `c ∈ C₁`): write the equality as `f '' class = union.colorClass c`
         with the image on the **left** (`Set.Subset.antisymm`'s first goal
         is then `image ⊆ class`), use `hv ▸ e₀.2` / `Subtype.ext hv` on the
         value equation out of `Set.mem_image`, and finish with
         `Set.ncard_image_of_injective _ hf`.
       * `mem_colorClass_coloringUnionCross`, `mem_hugeColourSet`,
         `card_sdiff_ge`, `card_le_card_sdiff_add`: the bookkeeping helpers
         for the next step.
       * **item (ii) DONE**: `case2Forb`/`case2List` (the forbidden colours
         `φ₁(N_{𝓗₂^left}(e))` and the lists
         `((C₁∪C₂)∖C_huge) ∖ φ₁(N_{𝓗₂^left}(e))`), `mem_case2Forb` /
         `mem_case2List` (their membership characterisations) and
         `case2_list_bound`: `|C(e)| ≥ d⫯(e) + (σ/4)n` from
         `(C₁∪C₂).card ≤ |C(e)| + |C_huge| + |forb e|`
         (`card_le_card_sdiff_add` twice), `|forb e| ≤ |N_{𝓗₂^left}(e)|`,
         `|C_huge| ≤ 32/β²` (`card_hugeColours_le`), `hsum` and the slack
         `1 + 32/β² ≤ (σ/4)n`; then `case2_large_colouring`: it builds `C₂`
         (`K := ⌊(1−3σ/2)n⌋₊`, room `K + |Cmed| ≤ n`, `|C₁| ≤ K`), fires
         Prop 6.9 on `𝓗₂^good ∪ 𝓗₁^good ∖ 𝓗_med` (`α₁ = σ/4`, `α₂ = β/5`),
         proves the cross-condition `φ₁(e₁) ≠ φ₂(e₂)` for intersecting
         `e₁ ∈ 𝓗₂^left`, `e₂ ∈ case2Right` (the lists exclude
         `case2Forb`), combines by `coloringUnionCross` over `case2_parts`,
         and verifies `hsingL` and `hsmallL` — i.e. exactly the input of
         `largeEdge_nonExtremal_of_largeColouring`.
       * **`precedingDegree_ge_fiber_add`** (the counting engine for the
         degree-splitting below): for an ordering `ord` of `𝓖` in which every
         edge of `𝓖₁` precedes every edge of `𝓖₂` (`hseg`), the preceding
         degree of `e ∈ 𝓖₂` is at least `|N_{𝓖₁}(e)|` plus the number of its
         preceding neighbours *inside* `𝓖₂` — proved by injecting
         `S₁ ⊕ S₂` into the preceding-neighbour subtype (the `Nat.card_sum`
         pattern of `natCard_interFiber_le_add`).  In particular, with the
         App-2 segmentation (now recorded as the new `BlocksOK` field
         `hseg₂`) it gives
         `|N_{Left₂}(e)| + d⫯_{Good₂}(e) ≤ d⫯_{Left₁}(e) ≤ (1−3σ)n`
         for `e ∈ Good₂`, and with the App-1 segmentation (`hseg₁`) the
         analogue `|N_{Left₁}(e)| + d⫯_{Good₁}(e) ≤ d⫯_{nonHuge}(e) ≤ γ₂n/3`
         for `e ∈ Good₁`.
       * **New counting helpers** (available for the assembly below):
         `natCard_subtype_mono` (a ⊇-monotone property gives a `Nat.card`
         bound on the subtype), `natCard_family_mono` (enlarging the family
         does not decrease the neighbour count) and
         `natCard_interFiber_add_le`
         (`|N_{𝓖₁}(e)| + |N_{𝓖₂}(e)| ≤ |N_{𝓖}(e)|` for disjoint subfamilies
         `𝓖₁, 𝓖₂ ⊆ 𝓖` — the *additive* companion of
         `natCard_interFiber_le_add`, proved by injecting the sum type into
         the neighbour subtype).  Also the block names
         `case2Good₂med`, `case2Good₁med` (needed because a binder
         `Nat.card {f : A \ B // P}` does not parse — see the parser note
         below).
       * **The `Nat.card` bridge** (fixes the blocker of the previous
         session): `natCard_ord_filter_eq` — two rankings of `α` with the
         same comparison relation give the *same* count of the elements below
         a fixed `x` (proved by `natCard_subtype_mono` in both directions,
         which unifies cleanly when both sides use the *same* bound variable
         `x`); `case2Pred₂` / `case2Pred₁` (the counts of the
         `ord₂`/`ord₁`-predecessors inside `𝓗₂^good`/`𝓗₁^good`) and
         `case2_pred₂_eq` / `case2_pred₁_eq` converting the *restricted*
         ordering's preceding degree into those counts.
       * **`case2_fwddeg_good₂` DONE**: for `e ∈ 𝓗₂^good ∖ 𝓗_med` and the
         concatenated ordering, `d⫯(e) + |N_{𝓗₂^left}(e)| ≤ (1−2σ)n`, from
         `precedingDegree_concatOrderingS_of_mem`, the restricted ordering,
         `case2_pred₂_eq`, the App-2 split (`precedingDegree_ge_fiber_add`
         with `hseg₂` + `hdeg₂`) and `hNsplit`/`hσn` by `linarith`.
         Two further Lean traps found here: (a) a membership
         `he : e ∈ case2Good₂med …` in a *definition* cannot be projected —
         extract `(Set.mem_sdiff.mp (by simpa only [case2Good₂med] using he)).1`
         first; (b) the `Nat.card` terms produced by
         `precedingDegree_ge_fiber_add` are spelled with
         `↑⟨↑e, heG₂⟩` (the lift of the given element) while the goal uses
         `↑e` — these are *definitionally* equal, and `exact_mod_cast hfib`
         converts the whole inequality in one step where
         `simpa only [case2Pred₂, Subtype.coe_mk] using …` fails.
       * **`case2_fwddeg_good₁` DONE** (the mirror of `case2_fwddeg_good₂`):
         `precedingDegree_concatOrderingS_of_notMem` → `natCard_family_mono`
         on `𝓗₂^good ∖ 𝓗_med ⊆ 𝓗₂^good` → the restricted ordering
         `ordG₁m ≤ ordG₁` → `case2_pred₁_eq` → the App-1 split
         (`precedingDegree_ge_fiber_add` with `hseg₁` + `hdeg₁`) →
         `natCard_interFiber_add_le` for
         `|N_{𝓗₂^good}(e)| + |N_{Left₂}(e)| ≤ |N_{𝓗₁^left}(e)|` → `hNsplit`
         and `hγm`.  Note (found here): to pass a `≤` through a *sum* whose
         second summand is replaced by a different (but larger) count, cast
         the ℕ chain first and then apply `add_le_add le_rfl` with the
         `case2Pred₁` bound — a single `exact_mod_cast` cannot do it.
       * **`case2_fwddeg_sum` DONE**: builds the two restricted orderings of
         `𝓗₂^good ∖ 𝓗_med` and `𝓗₁^good ∖ 𝓗_med` from `ord₂`/`ord₁`
         (`exists_restricted_ordering` twice each), the concatenated
         `ord' := concatOrderingS hcovR hdisjR ordG₂m ordG₁m` over the cover
         `case2Good₂med ∪ case2Good₁med = case2Right`, and dispatches on the
         two blocks, applying `case2_fwddeg_good₂`/`case2_fwddeg_good₁`
         (the unused `γ₂` in the Good₂ lemma must be given explicitly).
       * **`case2_Nsplit` DONE** (`hNsplit`): `case2Left ⊆ 𝓗_huge ∪ Left₂`
         follows from the cover `𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good` plus the
         disjointness of `𝓗₃` from `𝓗₂^good ∪ 𝓗₁^good` (and `W₂ ⊆ Left₂`),
         so `|N_{case2Left}(e)| ≤ |N_{𝓗_huge}(e)| + |N_{Left₂}(e)|`
         (`natCard_family_mono` + `natCard_interFiber_le_add`) and
         `|N_{𝓗_huge}(e)| ≤ |𝓗_huge| ≤ 32/β²` (`natCard_hugeEdges_le`).
         Needs the new def `case2HugeLeft₂` (`𝓗_huge ∪ Left₂`) because a
         binder `{g : A ∪ B // P}` does not parse either — the `∪`-analogue
         of the `\`-in-binder trap.
       * **Accounting subtlety for the final assembly** (discovered here):
         `case2_colouring_left` prescribes colour sets of sizes
         `⌈(1−ζ/1000)n⌉` and `⌈n/1500⌉` (hence
         `|C₁| ≤ ⌈(1−ζ/1000)n⌉ + ⌈n/1500⌉`), while `case2_large_colouring`
         needs `|C₁| ≤ K := ⌊(1−3σ/2)n⌋` so that `C₂` can fill `C₁` up to
         `K`; the paper's `(1−2σ)n` bound on `|C₁|` alone does **not**
         imply this (it is larger than `K`).  The hierarchy step must
         therefore arrange
         `⌈(1−ζ/1000)n⌉ + ⌈n/1500⌉ ≤ ⌊(1−3σ/2)n⌋`, i.e. roughly
         `ζ/1000 ≥ 3σ/2 + 1/1500` — e.g. by taking the prescribed `C''`
         smaller when `ζ` is small (claim B's alternative "colour every edge
         distinctly" only needs `|D| ≥ k`), or by noting that in the many-edge
         regime `ζ > 1 − δ^{1/4}`.  Recorded as the hypothesis `hC₁K`.
       * **`case2_data` DONE** (first glue line): fires `case2_colouring_left`
         (giving `C₁`, `φ₁` with `UsesColourSet`/`AlphaBounded (β/5)`/
         `|C₁| ≤ (1−2σ)n`/`Disjoint C₁ Cmed`) and `case2_fwddeg_sum` (with
         `case2_Nsplit`, `hσn`, `hγm`), returning `C₁, φ₁, kB, ord'` and the
         forward-degree-sum bound — exactly the two inputs of
         `case2_large_colouring`.
       * **CASE 2.1 IS CLOSED**: `case2_nonExtremal` proves
         `LargeEdgeNonExtremal` from the `BlocksOK` decomposition with
         `W₂ ≠ ∅` and the numeric hierarchy, by chaining `case2_data` →
         `case2_large_colouring` → `largeEdge_nonExtremal_of_largeColouring`.
         The two fixes it needed: the exact colour count of `C₁`
         (`C₁.card ≤ ⌈(1−ζ/1000)n⌉₊ + ⌈(1/1500)n⌉₊`, exported as the *fourth*
         conjunct of `case2_colouring_left`/`case2_data` so the `?_` bullets
         and `obtain` patterns keep their order — AlphaBounded / budget /
         size / disjoint) fed in as `le_trans hC₁size hC₁K`; and
         `(γ₁ := γ₁)` passed explicitly to `case2_data` (whose statement does
         not mention `γ₁`, so it cannot be inferred).  Still to do *beyond*
         Case 2.1: Case 2.2 and the parameter hierarchy, which must discharge
         `hC₁K` and the two Prop-6.9 margin pairs.
       * (Historical note on the plumbing:)
         `case2_large_colouring` needs `C₁.card ≤ ⌊(1−3σ/2)n⌋₊`, but
         `case2_colouring_left`/`case2_data` currently export only
         `(C₁.card : ℝ) ≤ (1−2σ)n` — which is *strictly weaker* (see the
         `hC₁K` ledger below).  The fix is to export the **exact size**
         `C₁.card ≤ ⌈(1−ζ/1000)n⌉₊ + ⌈(1/1500)n⌉₊` as an extra conjunct of
         `case2_colouring_left` and `case2_data` (its proof is the one-line
         `rw [Finset.card_union_of_disjoint hC'C''disj, hC'card, hC''card]`),
         and then pass `le_trans hC₁size hC₁K` in the `hC₁K` slot.
         **Careful with the conjunct position**: adding it at the *end* of the
         conjunction `A ∧ B ∧ C ∧ D` re-associates to
         `A ∧ (B ∧ (C ∧ (D ∧ E)))`, so the `?_` bullets (and the `obtain`
         patterns in `case2_data`/`case2_nonExtremal`) must be re-ordered to
         match — insert the size conjunct as the *fourth* conjunct (before
         the disjointness) to keep the bullet order
         AlphaBounded / budget / size / disjoint, or thread it with explicit
         `have`s.
       * **Remaining for Case 2.1**: one final lemma
         `case2_nonExtremal` (placing it at the **end of the file**, after
         `case2_large_colouring` — a lemma calling a later declaration is a
         forward-reference error) that chains
         `case2_data` → `case2_large_colouring` → `largeEdge_nonExtremal_of_largeColouring`.
         Its `case2_large_colouring` call needs **two independent Prop-6.9
         margin pairs** (learned while writing it):
         `h69m`/`h69b` for the family `case2H3med` with `α₁ = 1/6000`
         (Claim B) *and* `h69mσ`/`h69bσ` for the family `case2Right` with
         `α₁ = σ/4` (the `φ₂` list bound); since `1/6000 ≤ σ/4` fails for
         small `σ` these are separate hierarchy obligations, both of the form
         `2n/((β/5)(r₀−1)) < α₁n/4` and `#bigFinset < α₁n/2`.
         Argument order of `case2_large_colouring`: `hB hlin h2n hβ h2r₀
         hσ32 hsize hφ₁C hφ₁b hC₁ hdisj₁M ord' hsum h69m h69b hKroom hC₁K
         hslack hβc hn1 hγ₁σ hγ₁n`; of
         `largeEdge_nonExtremal_of_largeColouring`: `hn hsize hβ hγ₁σ hβn
         hdisjCL hbudgetL hφLC hsingL hsmallL hφmed hmedb hCmed` (the
         `hsize` there is the ℕ version `r₁ < edgeSize e`, obtained from the
         real one by `exact_mod_cast`).
       * (Superseded plan:) fire
         `case2_fwddeg_sum` on the `BlocksOK` data (with
         `hNsplit` from `case2Left ⊆ 𝓗_huge ∪ Left₂` + the huge-edge count,
         `hσn`, `hγm`), feed `ord'` and the sum bound to
         `case2_large_colouring`, and then to
         `largeEdge_nonExtremal_of_largeColouring` together with
         `case2_colouring_left` + `φ_med`.  (Superseded: the earlier plan
         below, kept for the two case-chains.)         * Then the assembly
         `case2_colouring_left` → `case2_large_colouring` →
         `largeEdge_nonExtremal_of_largeColouring` gives Case 2.1.
       * (Superseded notes, kept for the arithmetic:)
         (ii) one lemma `case2_large_colouring` producing
             `∃ C_large φL : (𝓗.largeEdges r₀).Coloring (Fin n)` with
             `φL.UsesColourSet C_large`, `|C_large| + |Cmed| ≤ (1−σ)n`,
             `Disjoint C_large Cmed` **and** the two properties `hsingL`,
             `hsmallL` of `largeEdge_nonExtremal_of_largeColouring`.  Its
             ingredients: `K := ⌊(1−3σ/2)n⌋₊`, `C₂ ⊆ Fin n ∖ (C₁ ∪ Cmed)`
             with card `K − |C₁|` (room hypothesis `K + |Cmed| ≤ n`);
             `C_huge := hugeColourSet 𝓗 𝓗₂^left β φ₁` with
             `|C_huge| ≤ 32/β²` (`card_hugeColours_le`); the lists
             `C(e) := ((C₁∪C₂)∖C_huge) ∖ φ₁(N_{𝓗₂^left}(e))` with
             `|C(e)| ≥ d⪯(e) + (σ/4)n` from
             `|C₁∪C₂| ≤ |C(e)| + |C_huge| + |N_{𝓗₂^left}(e)|`
             (`card_le_card_sdiff_add`), `hsum` and the slack
             `1 + 32/β² ≤ (σ/4)n`; Prop 6.9 on `𝓗₂^good∪𝓗₁^good ∖ 𝓗_med`
             (`kb`, `ord'`, `α₁ = σ/4`, `α₂ = β/5`); the cross-condition
             `φ₁(e₁) ≠ φ₂(e₂)` for intersecting `e₁ ∈ 𝓗₂^left`,
             `e₂ ∈ 𝓗₂^good∪𝓗₁^good` (the lists exclude
             `φ₁(N_{𝓗₂^left}(e₂))`); then `coloringUnionCross` over the
             cover `case2_parts` gives `φL`;
         (iii) inside that lemma, `hsingL` (a huge edge lies in
             `𝓗₂^left`, so its colour is in `C_huge`, so `φ₂` does not use
             it; `φ₁`'s class there is a singleton because `φ₁` is
             `β/5`-bounded and the class contains an edge of size
             `≥ βn/4 > βn/5`) and `hsmallL` (a class with no huge edge
             covers `≤ βn/4` in each part — `classVertexCount_le_of_alphaBounded`
             with `M = βn/4` for `φ₁` (no huge edge in the class) and for
             `φ₂` (`𝓗₂^good∪𝓗₁^good ⊆ nonHuge`) — hence
             `≤ βn/2 ≤ βn` by `classVertexCount_coloringUnionCross_le`).
             Then feed `largeEdge_nonExtremal_of_largeColouring`.
   (d) **Case 2.2** (`r₃ ≥ (1−δ)√n`): `LargeEdgeExtremal` via Corollary 6.7
       and Lemma 5.1 + Vizing — Claims 4–5; uses `(W₁1)`/`(W₁2)` to get
       `r₂ ≥ γ₂^{10} r₃`, hence `𝓗_med ⊆ 𝓗₁^good`.
       **IN PROGRESS** (`LargeEdgeCase22.lean`): the FPP-extremal volume
       witness (`extremal_witness_of_blocks` — needs the paper's
       `eqn:d3-upper-bound` `r₃ ≤ √(n/(1−4σ))` and the size-factor estimate
       `sizeFactor (3σ) 1 · √(n/(1−4σ)) ≤ (1+δ)√n`, both taken as explicit
       hypotheses), the volume→size conversion
       (`edgeSize_le_half_mul_of_volume`, `volume_singleton_le_of_notMem`,
       `edgeSize_le_half_mul_of_blocks`, whence NO edge of `𝓗` has size
       `≥ δn/2`), the class-coverage lemmas
       (`classVertexCount_le_of_ncard_le`, `classVertexCount_le_two_mul`,
       `case22_left_classes_le`), and Lemma 5.1 in the colouring API
       (`NearfullColouring`, `nearfullColouring_exists`,
       `nearfull_colouring_of`).  **Still to do**: the colouring `φ₁` of
       `𝓗₂^left = 𝓗_huge ∪ 𝓗₂^left` (Lemma 5.1 + `nearfull_colouring_of`),
       `C_huge`, `C_med`, the Claims `claim:bounded-colouring-extension2`
       and `claim:bounded-colouring-extension3` (two Prop 6.9 firings with
       the list assignments of the paper), `coloringUnionCross` glue and the
       verification of (i)–(iii) of `LargeEdgeExtremal`; then the
       `largeEdge_of_blocks` hypothesis `h22` can be discharged.
   (e) the parameter hierarchy of `LargeEdgeThmStatement`.

### ⚠ OPEN ISSUE: Case 2.1 needs the paper's `k`-split (found this session)

Discharging the `ζ`-dependent hypotheses of `largeEdge_of_blocks_full` revealed
that they are **jointly unsatisfiable unless `r₃` is small**:

* `hC₁K : ⌈(1−ζ/1000)n⌉₊ + ⌈(1/1500)n⌉₊ ≤ ⌊(1−3σ/2)n⌋₊` forces
  `ζ ≥ 2/3 + 1500σ`;
* `Corollary65Margins.hcodeg` + `hfinal` (with `B₀ ≥ sizeFactor(3σ,1)r₃ ≥ r₃`)
  force `r₃² ≲ (1−5ζ/6)n`, i.e. `r₃ ≲ 0.667√n` at the optimal `ζ = 2/3`;
* but Case 2.1 is only `r₃ < (1−δ)√n`, e.g. `r₃ = √n/2` (where `W₂` has
  `≈ 4n` edges) is allowed.

The paper avoids this with the `k`-split in `claim:before-W-colouring`
(`k := e(𝓗₃∖𝓗_med)`): if `k ≤ (ζ/1000−2σ)n` each edge of `𝓗₃∖𝓗_med` is given
its own colour (budget `(ζ/1000−2σ)n`, no lower bound on `ζ` needed); otherwise
`k > 2δ²n` and the volume computation gives `r₃ < δ^{1/4}√n`, so that
`ζ = 1 − r₃/√n > 1 − δ^{1/4} ≥ 2/3` — which makes both the `n/1500` budget and
`hcodeg` (`B₀² ≤ δ^{1/2}n(1+ε) ≤ (1−5ζ/6)n`) hold.

So: `ζ` must be the **instance-dependent** `1 − r₃/√n` (not a constant), and
`case2_colouring_left` must be split on `k`.  See
`Submission/EFL/LargeEdgeHierarchyWIP.txt` for the exact shape of the fix.

**PROGRESS on the fix (done):** both halves of the split are now in the
commons/cone:

* `volume_ge_card_mul_sq` — a subfamily's volume is at least
  `|𝓕|·(r−1)²/n²` when all its edges have size `≥ r`;
* `volume_H3_le` — `vol(𝓗₃) ≤ δ³` (disjointness of `𝓗₃` and the volume set
  `W₂` plus `vol ≤ 1`);
* `r₃_lt_sqrt_of_k_large` — the `k`-large branch of Case 2.1:
  `k > (ζ/1000−2σ)n ≥ 2δ²n` and `k(r₃−1)² ≤ δ³n²` give `(r₃−1)² < δn/2`,
  hence `r₃ < δ^{1/4}√n` (with `ζ = 1 − r₃/√n` this makes `ζ > 1 − δ^{1/4}`);
* `case2_H3med_distinct` — the `k`-small branch (each edge its own colour);
* `case2_H3med_split` — the resulting `𝓗₃∖𝓗_med` colouring with the budget
  `⌈(ζ/1000−2σ)n⌉₊` in both branches.

**RESOLVED (this session).**  The `k`-split is now in the code: the
`case2_H3_colouring` call inside `case2_colouring_left` has been replaced by
`case2_H3med_split`, the hypothesis `hbudget` of `case2_colouring_left` is the
*Nat* inequality
`⌈(1−ζ/1000)n⌉₊ + ⌈(ζ/1000−2σ)n⌉₊ ≤ ⌊(1−3σ/2)n⌋₊` (which is satisfiable for
every `ζ ∈ (0,1]`, unlike the previous `≤ (1−2σ)n` form, and implies the
conclusion `(C₁.card : ℝ) ≤ (1−3σ/2)n`), and `ζ` is now the
**instance-dependent** `1 − r₃/√n` throughout Case 2.1.

The *discharge* of the `ζ`-hypotheses is the new module
**`Submission/EFL/Case21.lean`**:

* `case21eps δ := δ/10⁵`, `real_exp_six_le : Real.exp 6 ≤ 414`,
  `five_sixth_exp_ge : 1/500 + 1/10⁵ ≤ 5/(6e⁶)` — the `3%` slack between the
  Molloy–Reed loss `5/(6e⁶) = 0.002066` and the `1/500` of Corollary 6.5;
* `case21_zeta` — `ζ := 1 − r₃/√n` satisfies `δ < ζ ≤ 1` in Case 2.1;
* the four `Corollary65Margins` fields at `ζ := 1 − r₃/√n`,
  `B₀ := ⌈sizeFactor (3σ) 1·r₃⌉₊`, `Δ := (1 + δ/10⁵)n`:
  `case21_margin_Dge`, `case21_margin_Dthr`, `case21_margin_hcodeg`,
  `case21_margin_hfinal`, each from `δ`-based margins
  (`r₃ ≥ 10⁷/δ`, `3τ^{1/4}(3σ) ≤ δ/10⁷`, `2δ² + 2σ ≤ δ/1000`,
  `C·(6/(5δ))^m ≤ n`);
* the room/budget transfers to the `ζ`-form (`Nat.ceil_le`,
  `Nat.ceil_lt_add_one` + `omega`);
* `hsize₃` (every edge of `𝓗₃∖𝓗_med` has size `≥ r₃`) from `BlocksOK`
  (`H₃ ⊆ 𝓗_huge ∪ 𝓗₂^left` plus the new margin `r₃ ≤ βn/4`);
* **`case2_nonExtremal'`** — Case 2.1 with *only* `δ/σ`-based numeric
  hypotheses, calling `case2_nonExtremal`.

`largeEdge_of_blocks_full` (`LargeEdgeCase22Main.lean`) now calls
`case2_nonExtremal'`, so the *only* remaining hypotheses of the full Theorem
6.1 case split (`largeEdge_of_blocks_full`) are the Case-2.2 ones plus
parameter/`n`-margins — no `ζ`, no `Δ`, no `B₀` any more.

**One deep-input change**: `MolloyReedStatement` (`LocallySparse.lean`) now
also records that the threshold is bounded by a polynomial in `1/ζ`
(`∃ C > 0, ∃ m, Δ₀ ζ ≤ C/ζ^m`) — the content of the literature's
`0 < 1/Δ ≪ ζ ≤ 1`.  This is exactly what `case21_margin_Dthr` consumes
(`ζ` ranges over `[5δ/6, 5/6]` here, so a *δ-uniform* threshold is needed,
and the polynomial bound supplies it).


### PROPOSITION 11.1 (`prop:pseudo_reservoir`) — DONE

`Submission/EFL/Pow2Edges.lean` + `Submission/EFL/ReservoirExistence.lean`
contain the proof of the paper's Proposition 11.1 (the existence of the
pseudorandom reservoir), together with the 2-edge/graph dictionary it needs:

* `otherVertex`, `eq_pair_otherVertex`, `otherVertex_unique`;
* `ncard_nbrs_eq_hypergraphDegree`, `ncard_inter_nbrs_eq`,
  `edgeCount_eq_edgesBetween` (the three counting identities);
* the event families `starEv`/`pairEv`/`crossEv` with `card_starEv`,
  `card_pairEv`, `card_crossEv`;
* the index type `ResIdx`, the events `resEv` and tolerances `resTol`;
* `exists_reservoir_core` (the probabilistic method, via the commons lemma
  `Commons.Combinatorics.FiniteSampling.exists_finset_sum_close`);
* `reservoir_sum_bound` (the union bound, from `exp_bound_linear`,
  `exp_bound_quadratic` and `card_pairs_le`);
* **`exists_pseudoReservoir_eventually`** — the final statement, using
  `Commons.Analysis.Real.reservoir_union_bound` for the numeric inequality.

Constants: the exponent for the degree/typicality events is
`ξ²/(2(ρ+ξ/3))·n`, for the regularity events `ξ⁴/(4(2ρ+ξ/3))·n²`; the counts
are `n + 2n|𝓥|` and `4ⁿ`.

### THEOREM 1.2 (`main-thm-2`) — the next milestone (in progress)

`Submission/EFL/MainThm2.lean` contains the statement
`MainThm2Statement`:

```
∀ δ > 0, ∃ n₀ ∃ σ > 0, ∀ n ≥ n₀, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
  (Δ(𝓗) ≤ (1-δ)n) → (#𝓗_ex(δ) ≤ (1-3δ)n) →
  ∃ k, (k : ℝ) ≤ (1-σ)n ∧ 𝓗.Colorable k
```

and the following **proved** pieces:

* **Step 1** (`volume_exEdges_lt_of`, `volume_exEdges_lt`,
  `exvol_arith_local`, using `Reservoir.volume_le_canon_card_mul_real`):
  for `0 < δ ≤ 1/4`, `2 ≤ n` and `#𝓗_ex(δ) ≤ (1-3δ)n`,
  `vol(𝓗_ex) < 1 - δ` once `n ≥ 1000/δ²`.  (The estimate is
  `vol ≤ (1-3δ)·x(x-1)/(n-1)` with `x = (1+δ)√n`; note the rounding trap
  found by a colleague: using `⌈(1+δ)√n⌉` in place of `x` **fails**, because
  the ceiling adds an `≈√n` term that the margin does not control — use the
  real bound `volume_le_canon_card_mul_real`.)
* **Colour relabelling** (`colourCast`, `colourCast_injOn`,
  `Coloring.relabel`, `Coloring.colorClass_relabel`): a colouring of a
  family that uses only a colour set `C ⊆ Fin n` with `C.card ≤ K` can be
  relabelled into `𝓖.Coloring (Fin K)`, with the colour classes at
  `colourCast C hK c` equal to those of `φ` at `c`.
* **Crossing count** (`card_largeEdges_meeting_le`): a small edge `e`
  (`|e| ≤ r₁`) meets at most `r₁·n/(r₀−1)` large edges (this is
  Claim 12.1's `EP2` as well).

**Remaining for Theorem 1.2** (the assembly; the deep inputs are
`MolloyReedStatement`/`KahnStatement`, which Theorem 6.1 already consumes):

1. Fix `δ` and set `δ' := min δ (1/4)`.  Apply
   `largeEdgeThmStatement_of_deep` at `γ₂ := δ'` to obtain
   `δ₀, σ₀, γ₁₀, β₀, R₁, R₀, N₀'`; take `δ'' := min δ' δ₀`,
   `σ := min σ₀ ...`, `γ₁ := min γ₁₀ ...`, `β := min β₀ ...`,
   `r₁ := R₁`, `r₀ := max R₀ ⌈2r₁/β⌉` (so that `2r₁/r₀ ≤ β`),
   `n₀ := max N₀' (⌈1000/δ'²⌉₊ + 100)`.
   **Parameter choices that work** (worked out, not yet formalised):
   `σ := min σ₀ (δ''/64)`, `γ₁ := min γ₁₀ (σ/4)`, `β := min β₀ (γ₁/4)`,
   `r₁ := max R₁ 2`, `r₀ := max R₀ (max (r₁+1) (⌈4r₁/β⌉₊+2))`,
   `α := 8(γ₁+β)`, `K := ⌊(1-σ)n⌋`.
2. From the hypothesis `#𝓗_ex(δ) ≤ (1-3δ)n` deduce
   `#𝓗_ex(δ'') ≤ (1-3δ'')n` (since `𝓗_ex(δ'') ⊆ 𝓗_ex(δ)`), and then
   `vol(𝓗_ex(δ'')) < 1-δ''`.  (Watch the `canonFinset` ↔ `ncard` bridge:
   `(canonFinset 𝓕).card = (𝓕).ncard` for `𝓕 : Set (Set (Fin n))`, via
   `Nat.card_eq_fintype_card` + `Fintype.card_ofFinset`.)
3. Apply the instance conclusion of Theorem 6.7 to
   `𝓗' := medLarge 𝓗 r₁ = 𝓗_med ∪ 𝓗_large` (linear, all edges `> r₁`).
   Rule out `LargeEdgeExtremal`: its witness `W ⊆ 𝓗' ⊆ 𝓗` consists of
   `δ''`-extremal edges, so `W ⊆ 𝓗_ex(δ'')` and
   `1 - δ'' ≤ vol(W) ≤ vol(𝓗_ex(δ'')) < 1 - δ''`, a contradiction.
   From `LargeEdgeNonExtremal` take `φ', C₁, Cmed` with
   `φ'.UsesColourSet C₁`, `|C₁| ≤ (1-σ)n`, `Cmed ⊆ C₁`, `|Cmed| ≤ γ₁n` and
   every medium colour in `Cmed`.
4. Relabel `φ'` into `Fin K`, `K := ⌊(1-σ)n⌋` (`Coloring.relabel` with
   `C := C₁`, using `Nat.le_floor`), giving `ψ'`; note
   `ψ'.labels f = colourCast C₁ _ (φ'.labels f)`.
5. Kahn (`KahnStatement`), applied to `𝓗_small := 𝓗.smallEdges r₁` with the
   lists
   `C(e) := {ψ'(f) : f ∈ 𝓗.largeEdges r₀, f ∩ e ≠ ∅} ∪ (Cmed.image (colourCast C₁ _))`.
   **Important correction found while writing this step**: with `Cmed`
   included in the lists one must take `α ≈ 8(γ₁+β)` rather than the paper's
   `α = 3β` — the size bound is `r₁n/(r₀−1) + γ₁n ≤ βn/2 + γ₁n` and
   `γ₁ ≫ β` in the hierarchy, so `α = 3β` is too small.  With
   `α := 8(γ₁+β)` (still `≪ δ`, so `(1+α)(1-δ) ≤ 1-σ` holds) and
   `β ≤ γ₁/4`, `r₀ ≥ 4r₁/β` (so `r₁/(r₀−1) ≤ β/2 ≤ γ₁/8`), the list bound
   `≤ αD/2` with `D := (1-δ)n` follows.  (The paper instead removes `Cmed`
   from the *colour set*, which avoids the issue but requires carrying an
   enumeration of `[(1-σ)n] ∖ Cmed` through the whole construction.)
   `Δ(𝓗_small) ≤ (1-δ)n` by `hypergraphMaxDegree_mono`, edge sizes `≤ r₁`
   by definition, and `(1+α)D ≤ K` for `n` large.
6. Combine `ψ'` on `medLarge 𝓗 r₁` with the Kahn colouring `ψ''` on
   `𝓗.smallEdges r₁` (they cover `𝓗`; use
   `union_small_medium_large`/`mem_small_or_med_or_large` and the
   cross-condition: if `e ∈ 𝓗_small`, `f ∈ 𝓗'` and `e ∩ f ≠ ∅`, then
   `ψ''(e) ≠ ψ'(f)` — for large `f` because `ψ'(f)` is in the list, for
   medium `f` because `φ'(f) ∈ Cmed`).  This yields `𝓗.Colorable K` and
   `K ≤ (1-σ)n` (`Nat.floor_le`).

### The §7–§12 definitions (`Reservoir.lean`)

`Submission/EFL/Reservoir.lean` now contains the paper's vocabulary used by
Sections 7–12, all on `Hypergraph (Fin n)` (a 2-edge family plays the role of
a graph):

* `Hypergraph.powFam i` (`𝓗^{(i)}`) and `Hypergraph.pow2` (`G = 𝓗^{(2)}`);
* `nbrs R v`, `degAt R v` (the 2-graph neighbourhood/degree), `Vplus 𝓗 x`
  (`V_+^{(x)}(G)`), `VgeNat`, `VeqNat`;
* `matchVert`, `Covers`, `PerfectCoverage`, `NearlyPerfectCoverage`;
* Definition 7.1's `Typical`, `UpperRegular`, `LowerRegular`; Definition
  7.3's `IsAbsorber` and `incidentTwo` (the paper's `G'`);
* Definitions 11.1–11.2's `IsPseudoReservoir`, `IsRegularising`;
* the `(ρ,ε)`-full condition `IsFull` and Definition 12.1's `IsTypeA`,
  `IsTypeB`, `medLarge`;
* the counting lemmas `volume_le_canon_card_mul` (integer edge-size bound)
  and `volume_le_canon_card_mul_real` (real bound), and Observation 7.4
  (`Typical.mono_del`, `IsAbsorber.mono_del`: deleting a sub-2-graph of
  maximum degree `≤ αn` costs `αn` in the typicality parameter).

**Next for §11** is Proposition 11.1 (`prop:pseudo_reservoir`, the existence
of a pseudorandom reservoir + absorber) — a probabilistic-method argument
using the weighted Chernoff bound; the fleet has been asked for the two
ingredients: `Commons.Probability.Chernoff.chernoff_two_sided_finite` (the
two-sided Chernoff bound on a finite product space) and
`Commons.Combinatorics.FiniteSampling.exists_finset_sum_close` (the
"there is a subset `R` with `|(R ∩ A_i).card - p·|A_i|| ≤ t_i` whenever the
sum of the Chernoff failure bounds is `< 1`" sampling lemma).

### §5 (FPP-extremal) and Lemma 5.1 — the Case-2.2 blocker, precisely located

**STATUS: RESOLVED.**  The whole §5 chain has been ported to minimal imports
in `Submission/EFL/Nearfull/` (six modules: `ExistsMaximalDisjointPairing`,
`ExistsUsefulPairsInClique`, `PairingOfUsefulFamily`,
`PairingOfUsefulFamilyClique`, `ExistsPairingOfSizeKFamily`,
`LinearNearfullColouring`), keeping the exact declarations (same names,
namespace `Commons.Combinatorics.Hypergraph`) and proofs of the commons files
but replacing `import Mathlib` by the minimal list computed with Mathlib's
`#min_imports in` command (the modules are now in `Submission.lean`'s import
cone and the whole build is green).  Two Mathlib facts were needed on top of
the `#min_imports` output: `Mathlib.Logic.Equiv.Fin.Basic` (for
`finProdFinEquiv`) in the two pairing-of-useful-family modules.  The port is
usable directly: `Commons.Combinatorics.Hypergraph.linear_nearfull_colouring`
is proved and in the cone.

The remainder of this section is the (now historical) record of the blocker.

**Lemma 5.1 (`extremal-case-lemma`)** — for `0 < 1/n₀ ≪ δ ≪ 1` and an
`n`-vertex linear `𝓗` with every `|e| ≥ (1−δ)√n`: a proper edge-colouring
with `n` colours, each colour on at most two edges — is **already proved in
the commons** as
`Commons.Combinatorics.Hypergraph.linear_nearfull_colouring` (plus its
supporting chain: `exists_maximal_disjoint_pairing`,
`exists_pairing_of_size_k_family`, `pairing_of_useful_family`,
`pairing_of_useful_family_clique`, `exists_useful_pairs_in_clique`,
`pairing_of_useful_pairs`, `nearfull_useful_caseA/B`,
`common_nbrs_bound`, `common_nbrs_card_le`, `lev_biUnion_powerset`,
`edges_size_ge_card`).

**Arithmetic obligations delegated to the fleet** (all three are commons-only
statements, no local definitions): `Data/Real/ceil_add_ceil_le_floor` (the
`hC₁K` ledger; the first version was *correctly refuted* — with
`⌈x⌉₊ ≤ x + 1` failing for `x < −1` the inequality is false, e.g.
`n = 1, ζ = 5000, σ = 4/3 − 1/2250`; the re-requested version adds
`ζ ≤ 1000`, which holds in our regime `ζ = 1 − r₃/√n ≤ 1`),
`Analysis/Real/two_mul_div_lt_of_mul_sub_one_gt` (both Prop-6.9 margin
pairs, at `α₁ = 1/6000` and `α₁ = σ/4`: `2n/((β/5)(r₀−1)) < α₁n/4` from
`40/(α₁β) < r₀ − 1`), and
`Combinatorics/Hypergraph/linear_nearfull_colouring_minimal_imports`
(Lemma 5.1 restated for the minimal-import commons, i.e. the §5 port below).

**BLOCKER**: its statement is on `Set (Set (Fin n))` — definitionally our
`Hypergraph (Fin n)` — so it is usable *in principle*, but the core files
of the chain begin with `import Mathlib` (`linear_nearfull_colouring`,
`exists_maximal_disjoint_pairing`, `exists_pairing_of_size_k_family`,
`exists_useful_pairs_in_clique`, `pairing_of_useful_family`,
`pairing_of_useful_family_clique`), which makes them **unimportable** here
(they export `_root_.Hypergraph`, breaking the fixed `Solution.lean`).  The
remaining files *are* minimal-import and safe
(`common_nbrs_bound`, `common_nbrs_card_le`, `nearfull_useful_caseA/B`,
`lev_biUnion_powerset`, `edges_size_ge_card`, and `pairing_of_useful_pairs`
whose head is `Mathlib.Combinatorics.Hall.Basic` — to be re-checked).
**HAZARD, verified by experiment (this session)**: minimality must hold
**transitively**.  The fleet's first port
(`Combinatorics/Hypergraph/linear_nearfull_colouring_minimal_imports`) is
*correct as mathematics* and passes the `#check Hypergraph` test in a *fresh*
file, but its head is
`import Submission.Commons.Combinatorics.Hypergraph.linear_nearfull_colouring`
— which itself starts with `import Mathlib`.  Adding it to `Submission.lean`
**fails** with
`error: Submission.lean:509:25: Ambiguous term Hypergraph; Possible
interpretations: _root_.Hypergraph (Fin n), ErdosFaberLovaszConjecture.Hypergraph (Fin n)`
(the ambiguity is reported where `theorem_1_1`'s statement mentions
`Hypergraph`, i.e. inside `Submission.lean` itself, so it is Submission's own
import list that matters, not only `Solution`'s).  The test that matters is
therefore: *add the import to `Submission.lean` and build* — a `#check` in a
standalone file is **not** sufficient.  Consequence: any port must be
reproved against minimal imports, not re-exported.
**Port attempt in this workspace** (parallel to the delegated one):
`Submission/EFL/NearfullPort.lean` contains the *proofs* of
`pairval`/`RelMatching`/`exists_maximal_rel_matching`/
`exists_maximal_disjoint_pairing` ported out of the commons file (namespace
`Submission.EFL.NearfullPort`, so nothing clashes), already adapted where the
minimal-import setting differs (`pairVal` is redefined by `if b = 0 then p.1
else p.2` because the `![·,·]` vector notation needs extra imports; `pairVal_mem`
proved by `fin_cases`).  It is **not** in `Submission.lean`'s cone and its only two gaps are: the module of `Finset.exists_maximal` and the
module giving `Fintype {e // e ∈ 𝓗}` for `𝓗 : Set (Set (Fin n))` (i) the
module providing `Finset.exists_maximal` (the name exists — signature
`{α} [LE α] [IsTrans α LE.le] {s : Finset α}, s.Nonempty → ∃ i, Maximal (fun x
=> x ∈ s) i` — but not in the probed modules; probe more or search the sources
by `lemma exists_maximal`), and (ii) the `Fintype ↥𝓗` / `DecidableEq ↥𝓗`
instances for an abstract `𝓗 : Set (Set (Fin n))`, which fail even under
`import Mathlib` — so pass them as **explicit typeclass hypotheses** of the
ported lemma (caller: `Fintype.ofFinite _`).  Once it builds, run the
definitive test (add to `Submission.lean`, build).

**Concrete next port** (also in flight, delegated): the generic core
`exists_maximal_rel_matching` was re-requested at
`Combinatorics/RelMatching/exists_maximal_rel_matching_minimal_imports`;
because its statement is generic over `V` (not `Fin n`), it *cannot* be
proved by citing the existing `Fin n`-specific file, which forces a genuine
port of the proof with minimal imports.  The remaining files of the chain
should be ported the same way, bottom-up.

**Arithmetic obligations — RESOLVED**: both landed in the commons and are
verified importable (head `Mathlib.Algebra.Order.Archimedean.Real.Basic`,
`#check Hypergraph` unambiguous):
* `Commons.Data.Real.ceil_add_ceil_le_floor` — the `hC₁K` ledger:
  `{ζ σ : ℝ} {n : ℕ} (hζ : ζ ≤ 1000) (h : 3 ≤ (ζ/1000 − 1/1500 − 3σ/2)·n) :
  ⌈(1−ζ/1000)n⌉₊ + ⌈(1/1500)n⌉₊ ≤ ⌊(1−3σ/2)n⌋₊`;
* `Commons.Analysis.Real.two_mul_div_lt_of_mul_sub_one_gt` — both Prop-6.9
  margin pairs, parametric in `α₁` (`40/(α₁β) < r₀−1`).

**Exact port list** (verified earlier): the unimportable files are
precisely the five whose head is literally `import Mathlib` —
`exists_maximal_disjoint_pairing` (151 lines),
`exists_pairing_of_size_k_family` (488),
`exists_useful_pairs_in_clique` (269),
`pairing_of_useful_family` (125),
`pairing_of_useful_family_clique` (133) —
together with the top file `linear_nearfull_colouring` (1489).  **Verified
importable** (no ambiguity for `Hypergraph`, checked with `#check Hypergraph`
against `ChallengeDeps`): `common_nbrs_bound`, `common_nbrs_card_le`,
`nearfull_useful_caseA/B`, `lev_biUnion_powerset`, `edges_size_ge_card` and —
importantly — `pairing_of_useful_pairs` (its head
`Mathlib.Combinatorics.Hall.Basic` does *not* pull in
`Mathlib.Combinatorics.Hypergraph.Basic`).
`exists_maximal_disjoint_pairing` also contains/uses
`exists_maximal_rel_matching` (generic, for any `Fintype` type), so its port
must bring the whole file along.
**Next action**: port those six files to minimal imports (mechanical: let
Lean report the missing imports; the statements and proofs are unchanged),
then restate Lemma 5.1 in the `ErdosFaberLovaszConjecture` API (as a
`𝓗.Coloring (Fin n)` with `(φ.colorClass c).ncard ≤ 2` for every colour,
which matches `LargeEdgeExtremal`'s "each colour on at most two edges"), and
use it for **Case 2.2** of Theorem 6.1 together with
`Commons.Combinatorics.SimpleGraph.vizing`.

### Resolved engineering questions

* `import Mathlib` cannot be used anywhere in the import cone of
  `Submission.lean`: it exports `_root_.Hypergraph`
  (`Mathlib/Combinatorics/Hypergraph/Basic.lean`), which makes the
  unqualified `Hypergraph` of the fixed `Solution.lean` ambiguous.  Any
  Mathlib module that does *not* (transitively) import that file is safe.
* The commons probability modules
  `Commons.Probability.Chernoff.prod_mgf_finite` and
  `Commons.Probability.Chernoff.chernoff_tail_finite` (finite-product-space
  weighted Chernoff bounds, proved by the fleet) **are** importable into
  this development — verified — so §8/§11 do not need a bespoke
  concentration package.  (`Commons.Data.Real.exp_one_add_le` too.)

## The remaining mathematical proof (mapping to the paper)

Fix a linear hypergraph `𝓗` on `n` vertices (large `n`).  By `BigEdges.lean`
assume no singleton edges.  The proof (see paper §3 "Overview", §6
"Preliminaries", §12 "Proof of Theorem 1.1") is organised as follows.

1. *Parameter hierarchy* (paper before Def. 3.1 / §12):
   `0 < 1/n₀ ≪ 1/r₀ ≪ ξ ≪ 1/r₁ ≪ β ≪ κ ≪ γ₁ ≪ ε₁ ≪ ρ₁ ≪ σ ≪ δ ≪ γ₂ ≪ ρ₂ ≪ ε₂ ≪ 1`.
   Formalisation: choose one fixed set of constants satisfying the strict
   inequalities (a fully explicit, finite choice), or use Skolemised
   parameters from the hypotheses of the main intermediate theorems.

2. *Split the edges into large / medium / small* (Def. "Types of hypergraphs",
   §12): edges of size ≈ √n (medium), size ≫ √n (large), size ≪ √n (small).
   Only the counts of edges of size `(1±o(1))√n` matter near the projective
   plane, so the thresholds can be polynomial functions of `n`.

3. *Colour the large and medium edges* — Theorem 6.7 (`large-edge-thm`,
   §6 "Colouring large and medium edges"): a proper colouring
   `φ : 𝓗_med ∪ 𝓗_large → [n]` with either (A) every colour class is a
   "`(ρ,ε)`-large matching" (non-extremal regime), or (B) all but `o(n)`
   edges of `𝓗_med ∪ 𝓗_large` receive colours used `n/√n ± o(n/√n)` times
   (extremal regime, close to a projective plane).  This theorem is proved
   with the help of §6.3–§6.7: reordering lemmas, locally sparse graph
   colouring (`Molloy–Reed` Thm 7.2, `Alon–Krivelevich–Sudakov` Thm 7.4,
   each needs its own formalisation) and the *vertex absorption* lemmas
   (§8): crossing/internal/huge-edge/difficult-edge absorption
   (Lemmas 8.6–8.12), themselves built on pseudorandom matching technology.

   **Status of §6.3:** Prop 6.9 (greedy list-colouring) is fully proved and
   machine-checked in `GreedyListColouring.lean` (`Prop69Instance`,
   `prop69Instance`, `prop69_colouring`, engine
   `greedy_colouring_hugeFirst`, reordering
   `exists_hugeFirst_reorder`/`fwddeg_le_of_reorder`).  **Status of §6.2:**
   the counting engine of Prop `fwdnbr` is formalised in
   `NeighbourSum.lean`: the neighbour-sum bound
   `∑_{f ∈ N(e)} (|f|−1) ≤ |e|(n−|e|)` (`sum_neighbour_size_sub_le`,
   via the cross-pair machinery `crossPairs`/`neighbourCrossPairs`,
   `neighbourCrossPairs_card`) and its natural corollaries
   (`card_neighbour_family_mul_le`, `card_neighbour_family_le`: a subfamily
   of `N(e)` with members of size ≥ ℓ has size ≤ |e|(n−|e|)/(ℓ−1)).
   **Next milestones in §6.2** (all on the exact definitions, in
   dependency order): (a) the full real-valued inequalities of Prop
   `fwdnbr` — `(1+α₁)m₁ + m₂/(1+α₂) ≤ n + (1+α₂)n/(r−1−α₂)` and the
   derived `m₁ ≤ (τ + (1+α₂)(1+α₂r)/(r−1−α₂))·n/α₁` — restated over
   `Finset` subfamilies `F₁`, `F₂` of `N(e)` with real size thresholds
   (**status: **Prop `fwdnbr` is COMPLETE** — both inequalities are proved
   in `NeighbourSum.lean`: (i) as `fwdnbr_inequality1`, assembled from
   `fwdnbr_sum_alpha` (α), `fwdnbr_union_upper`, `fwdnbr_beta` (β) and
   `fwdnbr_gamma` (γ, the divided `fwddeg-inequality2`); (ii) as
   `fwdnbr_inequality2` — the `τ`-far-bound
   `m₁ ≤ (τ + (1+α₂)(1+α₂r)/(r−1−α₂))·n/α₁` under
   `m₁ + m₂ ≥ (1−τ)n` and `α₁ > 0` — writing (i)'s left side as
   `(m₁+m₂) + α₁m₁ − (1−1/(1+α₂))m₂`, dropping `m₁+m₂ ≥ (1−τ)n`, using
   `1 − 1/(1+α₂) ≤ α₂` (`one_sub_inv_le`), bounding `α₂m₂` via
   `fwdnbr_gamma`, and dividing by `α₁ > 0`)
   (`hbig : ∀ f ∈ F₁, ((1+α₁)·r : ℝ) ≤ (edgeSize f : ℝ)`,
   `hmed : ∀ f ∈ F₂, (r/(1+α₂) : ℝ) ≤ (edgeSize f : ℝ)`, `hFᵢ : Fᵢ ⊆
   neighbourEdges 𝓗 e`, `hdisj : Disjoint F₁ F₂`, `hcond :
   (1+α₂ : ℝ) < r`, `mᵢ := (Fᵢ.card : ℝ)`, `r := (edgeSize e : ℝ)`),
   proved from the real version `sum_neighbour_real_le` of the sum lemma
   (**proved**: it is the real cast of `sum_neighbour_size_sub_le`, with the
   per-term `Nat.cast_sub` rewrite `↑(edgeSize f − 1) = (edgeSize f : ℝ) − 1`
   for `f ∈ N(e)` using `edgeSize f ≥ 1` from `f ∩ e ≠ ∅`) by:
   (α) lower-bound `∑_{F₁∪F₂}((edgeSize f : ℝ) − 1)` by
   `m₁·((1+α₁)r − 1) + m₂·(r/(1+α₂) − 1)` (disjoint union + per-member
   bounds); (β) divide by `r > 0` to get
   `(1+α₁)m₁ + m₂/(1+α₂) ≤ n − r + (m₁+m₂)/r`; (γ) bound `m₁+m₂` via
   `(r/(1+α₂) − 1)·(m₁+m₂) ≤ ∑_{F₁∪F₂} ≤ rn`; (δ) substitute.  For the
   division arithmetic the pattern that works is
   `apply le_of_mul_le_mul_right _ hpos` then `calc` with the final step
   `by field_simp [hpos.ne']` (probes confirmed; plain `nlinarith` cannot
   divide).
   (b) the reordering lemma itself (`reordering-lemma`): every linear
   hypergraph with edges of size ≥ r₁ has an ordering which is either
   "good" (`fwddeg ≤ (1−τ)n` everywhere) or exposes a set `W` of similar
   large edges with big volume — **status: statement pinned, volume
   machinery proved, and **Block I (the minimal forward-degree walk)
   PROVED** in `Submission/EFL/Reordering.lean`** (module docstring
   decomposes the proof into Blocks I–VI; `volume`/`volume_nonneg`/
   `volume_mono`/`volume_le_one` (vol ≤ 1 for linear hypergraphs), the
   predicates `GoodOrdering`/`OrderingGoodness`/`OrderingBySize`/
   `WMaxSize`/`WVolume`/`VolumeWitness`, the instance statement
   `ReorderingInstance`, Block I's `AdmissiblePair`/`predEdge`/
   `fwddeg_zero_of_first`/`O1_of_pred`/`O2_of_pred`/`good_of_first_admissible`/
   `blockI`, and the initial admissible pair — the size-non-increasing
   ordering `SizeLess`/`sizeRank`/`sizeOrder` (with `sizeLess_total`,
   `sizeRank_mono`, `sizeRank_injective`, `sizeOrder_ge_size`,
   `lastEdge`, `sizeOrder_admissible_last`, `sizeOrder_blockI`) — are all
   machine-checked, and **Blocks II–III (good case + volume-set setup)
   PROVED**: `VolumeSet`/`mem_VolumeSet` with `volumeSet_mem_self`,
   `volumeSet_le_rank`, `volumeSet_ge_self`, `volumeSet_maxSize` (W1) and
   `blockIII_setup`; **Block IV (fully
   PROVED)**: `segmentPrefix`/`segmentPrefix_mono`, `nbrsInPrefix` with
   `eStar_mem_nbrsInPrefix`, `fwdnbr_subset_nbrsInPrefix`,
   `card_nbrsInPrefix_ge_fwddeg`, `nbrsAhead_ge_fwddeg`,
   `card_nbrsInPrefix_le_degree`, and the open statement
   `BlockIVStatement`/`NeighbourAheadBound`; the **block rotation**
   `rotateEquiv` over ranks (`rotateVal`/`rotateInv` with the inverse
   identities, `rot_of_lt`/`rot_of_between`/`rot_of_gt`,
   `rotateVal_strict`/`rotateVal_reflect`, `old_rank_le_of_rot_le`/
   `old_rank_ne_a_of_rot_le`/`old_rank_gt_b_of_new_rank_ge`,
   `rotate_rank_le_b_iff`/`rotate_rank_le_iff_of_gt_b`,
   `rotate_rank_val`/`rotate_rank_eStar`, `rotate_rank_of_gt_b`), the
   exact new forward degree `fwddeg'(e) = |N(e)∩H^{⪯e*}|`
   (`rotate_fwdnbr_eq_nbrsInPrefix`/`rotate_fwddeg_e`/
   `rotate_fwddeg_e_real_le_of_fail`), the prefix loss
   `blockIV_prefix`/`blockIV_prefix_card`, (O1)+(O2) preservation
   (`blockIV_O1`/`blockIV_O2`) with fwddeg preservation of edges past
   `eStar` (`rotate_fwdnbr_of_rank_gt_b`/`rotate_fwddeg_of_rank_gt_b`),
   the rotation step `blockIV_rotation`, the global minimal admissible
   pair (`exists_minimal_admissible`/`exists_minimal_admissible_of_fintype`
   by `Nat.find`, with `segmentPrefix_predEdge`/
   `segmentPrefix_predEdge_card_lt`), and the paper's eq. (6.3)
   `blockIV_of_minimal` plus `minimal_admissible_dichotomy` (good ordering
   ∨ eStar at rank ≥ 1 with `fwddeg(e*) > (1−τ)n` and `BlockIVStatement`);
   **Block V, part 1 (PROVED)**: the size-truncated neighbourhood
   `XSmall τ K ord eStar` = `X` (`mem_XSmall`, subsets
   `XSmall_subset_preceding`/`XSmall_subset_neighbourEdges`, (O2)-sizes
   `prefix_size_ge`/`precedingNeighbour_size_ge`/`XSmall_size_ge`),
   application 1 of `fwdnbr_inequality2` (`blockV_boundNminusX`:
   `|N^⪯(e*)∖X| ≤ (τ + 1/(r−1))·n/(K√τ)` via the partition
   `blockV_X_from_partition`), `blockV_X_lower` (`|X| ≥ (1−τ)n − |N^⪯∖X|`),
   and eq. (6.4) `blockV_X_bound`: `|X| ≥ (1−τ−2√τ/K)·n` under the margin
   `1 ≤ τ(r−1)` (`one_div_sub_one_le`, `boundNminusX_le`);
   **Block VI, part 2, step 1 (PROVED, COMPLETE)**: the eq. (6.7)
   vocabulary (`fwdnbrNbrs` = `N(e)∩fwdnbr(e*)`, `blockVIN₁`/`blockVIN₂`
   with membership), the disjoint partition (`blockVIN₁_disjoint_N₂`,
   `blockVIN₁_union_N₂`, `blockVIfwdnbr_card`), the **N₂ bound**
   `blockVI_N₂_bound` (`|N₂| ≤ (|e|−1)(|e*|−1)` via `f ↦ (u_f, w_f)`
   injective into `(e∖{v})×(e*∖{v})`), the **N₁ bound**
   `blockVI_N₁_bound` (`|N₁| ≤ n/(r−1)` via the pairwise-disjoint
   leftovers `(verts f).erase v` summed by `Finset.disjiUnion`), and the
   real combination **eq. (6.7) `blockVI_fwdnbrNbrs_le`**:
   `|N(e)∩fwdnbr(e*)| ≤ n/(r−1) + (|e|−1)(|e*|−1)`, and the margin form
   `blockVI_fwdnbrNbrs_margin` (`≤ τ^{1/4}n/K + (1+K√τ)r²` under
   `K ≤ τ^{1/4}(r−1)`, `e ∈ X`); **Block VI, part 2, step 2 (PROVED)**:
   the counting set `B := blockVIB` = `W∖(N(e*)∪{e*})` (`mem_blockVIB`,
   `blockVIB_disjoint_eStar`, `blockVIB_subset_prefix`), `N(e)∩B =
   (N(e)∩H^{⪯e*})∩B` (`blockVI_NB_eq_inter`), the containment
   `A∖B ⊆ (A∖W) ∪ (N(e)∩fwdnbr(e*)) ∪ {eStar}`
   (`blockVI_A_minus_B_subset`), the cardinality skeleton
   `blockVI_eq66_card`, and **eq. (6.6) `blockVI_eq66`**: for `e ∈ X`,
   `|N(e)∩B| ≥ (1−τ−7τ^{1/4}/K)n − (1+K√τ)r² − 1` (chains eq. (6.3),
   (6.5), (6.7)); **Block VI, part 2, step 3 (PROVED)**: eq. (6.8)
   `blockVI_eq68` (`|N(f)∩X| ≤ sizeFactor·r²` for `f ∈ B`, via
   `X ⊆ N(e*)`, `card_commonNeighbours_disjoint_le`, `mem_VolumeSet`),
   `neighbourEdges_symm`, and the **double count**
   `blockVI_doubleCount` (`Σ_{e∈X}|N(e)∩B| = Σ_{f∈B}|N(f)∩X|` via the
   commons `sum_card_filter_comm`); **step 4 (PROVED)**: the **|B| lower
   bound** `blockVI_B_lower` (`|X|·((1−τ−7τ^{1/4}/K)n − (1+K√τ)r² − 1) ≤
   |B|·sizeFactor·r²`, summing eq. (6.6) over X and eq. (6.8) over B
   through the double count, with the helper `XSmall_mem_size`);
   **step 5a (PROVED)**: `sizeFactor_ge_one_sqrt` (`1+K√τ ≤ sizeFactor`),
   `XSmall_subset_VolumeSet` (`X ⊆ W`), `XSmall_disjoint_blockVIB`
   (`X ∩ B = ∅`), `blockVI_W_ge_B_add_X` (`|B| + |X| ≤ |W|`);
   **step 5b (PROVED)**: `blockVI_slack_nonneg`,
   `blockVI_bracket_nonneg`, and the |W| lower bound `blockVI_W_lower`
   (`|W| ≥ (1−τ−2√τ/K)·(1−τ−7τ^{1/4}/K)·n²/(sizeFactor·r²)` under the
   margins `hAmar`, `0 ≤ q` and the eq. (6.4) bound);
   **step 6a (PROVED)**: `blockVI_volume_term_ge` (per-`e ∈ W` summand
   `|e|(|e|−1) ≥ r(r−1)`) and `blockVI_volume_sum_ge`
   (`|W|·r(r−1) ≤ Σ_{e∈W} |e|(|e|−1)`);
   **step 6b (PROVED)**: `blockVI_cast_sub_one` and
   `blockVI_frac_n_sub_one_ge`;
   **step 6c (PROVED)**: the (W2) volume bound **`blockVI_WVolume`**
   (`volBound τ K ≤ volume 𝓗 (VolumeSet τ K ord eStar)` from the |W|
   bound `hW`, `blockVI_volume_sum_ge`, the margin
   `(1−τ−2√τ/K)(1−1/r) ≥ 1−τ−7τ^{1/4}/K`, `0 ≤ q`, `2 ≤ n`) — the |B|/
   |W|/volume part of Block VI is complete;
   **assembly part 1 (PROVED)**: `ReorderingInstance` now carries the
   explicit margin block `ReorderingMargins r₁ τ K` (the concrete
   `0 < 1/r₁ ≪ τ, 1/K`), with accessors `rm_q_pos`…`rm_hfin` and the
   transfers to edge sizes (`rm_mar_of_le`, `rm_M1_of_le`, `rm_M2_of_le`,
   `rm_Amar_of_le`, `rm_hfin_of_le`);
   **the reordering lemma (Lemma 6.2) is PROVED**:
   `reorderingLemma` (`ReorderingInstance`) — empty case trivial, else the
   minimal admissible pair + dichotomy, the Block-VI chain
   (`blockV_X_bound`, `blockVI_W_lower`, `blockVI_WVolume`) with the
   transferred margins, assembled into a `VolumeWitness`;
   **Theorem 6.1 preparation, step 1 (PROVED)**: the subfamily firing
   template `reorderingLemma_of_subfamily` (the reordering lemma applied
   to any `𝓖 ⊆ 𝓗`; linearity via `hlin.mono`, sizes via `hsub`) — the
   shape of every Fig. 3 application;
   **step 2 (PROVED)**: margins follow from large r₁ —
   `margin_tau_of_bound`, `margin_mar_of_bound`, `margin_M1_of_bound`,
   `margin_M2_of_bound`, and the package
   `ReorderingMargins_follows_from_large` (given `0 < q` and the seven
   raw margin bounds at `r := (r₁ : ℝ)`, `ReorderingMargins r₁ τ K`
   holds) — the `r₁ ≥ R(τ,K)` discharge template of the App-1/2/3
   firings;
   **step 3a (PROVED)**: App-3 constants `app3tau = 1−1/2000`,
   `app3K = 2000²` and the bounds on `τ^{1/4}`, `√τ`
   (`app3_tauQuarter_ge_half`, `app3_sqrt_le_one`,
   `app3_tauQuarter_le_one`, `app3_sqrt_ge_quarter`, `app3_tau_pos`)
   feeding the App-3 margin discharge;
   **step 3b (PROVED)**: `app3_margins r₁` — for `(r₁ : ℝ) ≥ 10⁸`,
   `ReorderingMargins r₁ app3tau app3K` (each `hLᵢ` discharged from the
   root bounds; `hL6` by the explicit chain
   `u(1−1/r)−q = (u−q)−u/r ≥ (u−q)/2 ≥ 0`); with this, the App-3 firing
   of `reorderingLemma_of_subfamily` on `𝓗₃` is a direct instantiation;
   **step 4 (PROVED)**: the **App-3 firing** `app3_firing` — the
   reordering lemma instantiated at `(τ, K) = (app3tau, app3K)` on any
   subfamily (the Fig. 3 `𝓖 := 𝓗₃` shape), giving `GoodOrdering app3tau
   ord ∨ VolumeWitness app3tau app3K ord`;
   **step 5 (PROVED)**: the volume-contradiction arithmetic
   `app3_volume_contradiction` (`vol(W₂) ≥ 1−δ³`, `vol(W₂)+vol(W′) ≤ 1`,
   `δ ≤ vol(W′)`, `0 < δ < 1` ⟹ `False`) — the App-3 hinge that forces
   the good case;
   remaining: the `𝓗₃` plumbing (transport of reordering `W′`-volumes to
   `𝓗`-subfamily volumes, disjointness, `volBound ≥ δ` discharge);
   **step 6 (PROVED)**: the **App-2 firing** — `app2tau (σ) := 3σ`,
   `app2K = 1`, `app2_firing` (reordering lemma at `(3σ, 1)` on any
   subfamily, margins carried as conjuncts), giving `GoodOrdering (3σ)
   ord ∨ VolumeWitness (3σ) 1 ord`;
   **step 7 (PROVED)**: **volume transport** `volume_of_subfamily`
   (volume of a subfamily-finset equals the ambient volume of its
   inclusion image) — the hinge comparing reordering `W′`-volumes with
   ambient `𝓗`-subfamily volumes;
   **step 8 (PROVED)**: **volume additivity** `volume_disjoint_add` and
   the bound `volume_disjoint_le_one` (`vol(S₁)+vol(S₂) ≤ 1` for
   disjoint subfamilies of a linear hypergraph) — the
   `vol(W₂)+vol(𝓗₃) ≤ 1` input of the App-3 contradiction;
   **step 9 (PROVED)**: the **wiring instantiation** — `subfamilyImage`,
   `volume_subfamilyImage`, `subfamilyImage_disjoint`, and
   `volume_wiring` (subfamily-finsets with disjoint ambient images have
   total volume ≤ 1), i.e. `vol(W₂)+vol(𝓗₃) ≤ 1` for the Fig. 3
   families;
   **step 10 (PROVED, this session)**: the **subfamily concatenation** —
   `SubfamilyConcat.lean`'s `setSumEquiv` (a disjoint cover is a sum, with
   `natCard_eq_add_of_cover`), `concatOrderingS` with its rank
   characterisations and the *exact* preceding-degree transfer
   `precedingDegree_concatOrderingS_of_mem` / `_of_notMem`, packaged as
   `exists_ordering_of_disjoint_cover`: the two-part concatenation shapes of
   both Theorem 1.3 (`W_i`-blocks and good blocks) and Figure 3
   (`𝓗₃, W₂, 𝓗₂^good, 𝓗₁^good` are obtained by iterating it).
   **step 11 (PROVED, this session)**: the **stability loop's infrastructure**
   — `StabilityLoop.lean`: the subfamily-volume bridge `volume_finFam`
   (a `𝓗`-finset's volume is its subfamily's volume), monotonicity
   `volume_subfamily_mono` and additivity `volume_subfamily_union`; the
   three blocks of one reordering step (`rankBelow ord fStar`,
   `midBlock ord fStar eStar`, `goodBlock ord eStar`) with
   membership/subset/disjointness, the cover `cover_blocks`, (O1) on the good
   block (`goodBlock_precedingDegree_le`), (O2) on the middle block
   (`midBlock_size_ge`), the step-data extraction `exists_step_data`
   (`|e*| ≤ |e| ≤ A|e*|` on the middle block and `vol([f*,e*]) ≥
   volBound τ K`), and `exists_restricted_ordering` (the induced ordering of
   a subfamily, with no larger preceding degrees; via
   `Commons.Data.Finset.restrict_ordering`).  The `VolumeWitness` of the
   reordering lemma now records `eStar ∈ W` (needed to make `|e*|` the
   minimum size in `W`).  Next: the list-indexed decomposition and the
   induction on `vol ≤ m·volBound`, then the Theorem-1.3 assembly.
   **step 10 (PROVED)**: the two volume bounds
   (`volume_ge_one_sub_of_witness`, `volume_ge_delta_of_witness`) and
   the **App-3 collapse** `app3_volume_collapse` (`vol(W₂) ≥ 1−δ³`,
   `vol(W′) ≥ δ`, ambient disjointness ⟹ `False`) — App 3's disjunction
   collapses to `GoodOrdering app3tau ord` (`fwddeg ≤ n/2000` on
   `𝓗₃`);
   **step 11 (PROVED)**: the **Fig. 3 rank families** `rankAbove`/
   `rankBelow` (membership criteria, inclusions `⊆ 𝓖`), the disjointness
   core `disjoint_rankAbove_rankBelow`, and
   `subfamilyImage_disjoint_of_disjoint` — supplying the ambient
   disjointness of `app3_volume_collapse`;
   **step 12 (PROVED)**: the **App-3 closing instantiation** — `nonHuge`
   (`𝓗′`) and `app3_closing` (`W₂` in the `f*`-span `rankAbove ord₂ f*`
   with `vol ≥ 1−δ³`, `W′` in the complementary `rankBelow` with
   `vol ≥ δ` ⟹ `False`): the Fig. 3 shape end-to-end, so supplying the
   App-2/App-3 witnesses collapses the App-3 firing to
   `GoodOrdering app3tau ord` on the residual family — App 3 closed;
   **step 14 (PROVED)**: **`app3_good`** — with the App-2 volume set `W₂` in
   the `f*`-span (volume `≥ 1−δ³`) and the App-3 threshold
   `δ ≤ volBound app3tau app3K`, the complementary family
   `rankBelow ord₂ f*` (the paper's `𝓗₃`) admits a *good* ordering at
   parameter `app3tau`: the reordering lemma on `𝓗₃` plus
   `app3_volume_collapse` rule out the volume alternative;
   **step 13 (PROVED)**: `exists_finset_rankAbove`/`exists_finset_rankBelow`
   (retyping volume sets into the `f*`-span and its complement);
   remaining: wire the concrete `𝓗₁^left`/`ord₂`/`f*` and the huge-edge
   case, then App 1 and §6;
   **Block V, part 2 (PROVED)**: application 2 of `fwdnbr_inequality2`
   — τ^{1/4}-arithmetic (`tauQuarter_sq`/`tauQuarter_pow_four`/
   `tauQuarter_pos`/`tauQuarter_le_one`), the size-factor comparison
   `sizeFactor_ge_product` (`(1+K³τ^{1/4})(1+K√τ) ≤ sizeFactor`, raw
   `blockV_product`), the far-bound algebra `blockV_app2_algebra`, the
   containment `outsideVolumeSet_subset_big` (`N(e)∩H^{⪯e*}∖W ⊆ F₁`), and
   **eq. (6.5) `blockV_app2`**: for `e ∈ X`,
   `|(N(e)∩H^{⪯e*})∖W| ≤ 6τ^{1/4}n/K`, under the concrete margins
   `1+K√τ ≤ |e|/2` and `2(1+K√τ) ≤ K²√τ·|e|`;
   remaining: Block VI (eqs. (6.6)–(6.8): per-`e ∈ X` bound
   `|N(e)∩(W∖N(e*))| ≥ (1−τ−7τ^{1/4}/K)n − (1+K√τ)r²` via the counting
   lemmas `|N₁| ≤ n/(r−1)` (pairwise-disjoint leftovers of edges sharing
   `e∩e*`) and `|N₂| ≤ (|e|−1)(|e*|−1)` (injection into the product of
   the two edge-vertex sets), the per-`f` bound
   `|N(f)∩X| ≤ |f||e*| ≤ (1+3τ^{1/4}K⁴)r²`, the double count (commons
   `Finset.sum_card_filter_comm`), the |W∖N(e*)|/|W| lower bounds and the
   (W2) volume bound `WVolume` of `VolumeSet`), and the assembly of
   `ReorderingInstance` from `minimal_admissible_dichotomy` +
   `blockIII_setup` + `blockV_X_bound` + `blockV_app2` + Block VI);
   (c) corollaries: an ordering by decreasing
   size gives `fwddeg(e) ≤ (1 + 1/(|e|−1))n`, hence the classical bounds
   `χ′(H) ≤ 2n + 1` / `(1 + 1/(r₁−1))n + 1` for linear `H` (a greedy
   corollary of Prop 6.9); (d) the locally-sparse corollaries
   (`sparsity-corollary`, `aks-sparsity-corollary`) whose proofs bound the
   maximum degree and the codegrees of the line graph and invoke Molloy–Reed
   / AKS (each an external theorem to be built on `SimpleGraph`).

4. *Colour the remaining small edges* (not in the reservoir) — §9 "Nibble
   Lemma" (Lemma 9.1), "Main colouring lemma" (Lemma 9.6), "Leftover
   colouring lemma" (Lemma 9.12), using the Rödl-nibble technique
   (pseudorandom matchings, e.g. Ehard–Glock–Joos Thm 6.2, needs a full
   formalisation) applied to the small edges of each colour with respect to
   the `φ`-colouring.

5. *Reservoirs* — §11 "Constructing reservoirs": Lemma 11.2
   (regularising reservoir) and Lemma 11.5 (regularising lemma) provide a
   sparse set of "reserved" edges with prescribed quasirandom behaviour,
   used by both the absorption and the nibble arguments.

6. *Optimal edge-colourings* — §10: Hall-based finishing lemma (Lemma 10.2)
   and edge-colouring pseudorandom graphs (Glock–Kühn–Osthus Thm 10.8),
   used to colour leftover "difficult" matchings at the end.

7. *Conclusion* — §12: assemble the pieces for the three "Types"
   `A₁` (not close to a degenerate plane / full case), `A₂` (full case),
   `B` (extremal case) and obtain `n` pairwise edge-disjoint matchings
   covering all edges, i.e. an `n`-colouring of `𝓗`.

## Progress on §10 and §11 (this stretch of work)

* **§11, Lemma 11.2 (`lem:reg_reservoir`) — PROVED** in
  `Submission/EFL/RegReservoir.lean`, conditional only on the new deep input
  `GFactorStatement` (Lovász's `(g,f)`-factor theorem, stated in
  `Submission/EFL/GFactor.lean`).  The proof follows the paper exactly:
  the clique `S ⊆ V^{(n-1)}(G)`, the reserved family `R'`, the induced graph
  `G[W] - Rabs - R'`, the functions `f = ⌊ρ d_G + ξn - d_{Rabs} - d_{R'}⌋`,
  `g = f - 1`, the two-case verification of the Lovász condition
  (`lovasz_condition`) and the `(R1)`/`(R2)` degree estimates.  Numeric
  margins used: `1 ≤ εn`, `1 ≤ 5εn`, `ρ ≤ 1/100`, `25 ≤ ρn`,
  `20ε ≤ ρ²`, `20ε + ξ ≤ ρ/2`, `ξ ≤ ρ/2`, `2 ≤ ξn`.
* **§10, Proposition 10.3 (`obs:del_lowerreg`) — PROVED** in
  `Submission/EFL/LowerReg.lean` (both parts).  This required the counting
  lemmas `edgeCount_eq_ncard` (the `Set.ncard`-form of `edgeCount`, which
  sidesteps all `Finset.filter` decidability-instance problems),
  `edgeCount_union_le` and `edgeCount_mono_sets`, and the self-regularity
  predicate `SelfLowerRegular`.
* **§12, `claim:easyobs` (EP1) — PROVED** in `Submission/EFL/Obs12.lean`.
* **Commons in flight**: `Commons.Combinatorics.SimpleGraph.vizing_two_max`
  (the refinement of Vizing: if at most two vertices have degree `D` then
  `χ' ≤ D` — needed by Lemma 7.12's proof) and
  `Commons.Data.Real.ceil_sub_nat`.

* **§10, Theorem 10.8 (`thm:optcol`) as `GKOStatement`** (deep input) and
  **Corollary 10.13 (`cor:optcol`) in the even case** — both in
  `Submission/EFL/OptCol.lean`.  The even case is complete:
  `maxDegree_ge_of_selfLowerRegular` (`Δ ≥ (p-3ε)n` from lower regularity),
  `maxDegree_le_sum_sub` (`Σ_v(Δ-d_v) ≥ Δ`), the minimum-degree vertex and
  the `(def_ineq)` condition, then `GKOStatement`.
  **TODO (odd case)**: for odd `n` the paper adds a new vertex `v*` joined
  to `t := ⌊Δ - 2ηn⌋` vertices of degree `< Δ`, obtaining `G*` on `n+1`
  vertices with `Δ(G*) = Δ`, `δ(G*) = t`,
  `Δ(G*) - δ(G*) ≤ 3η(n+1)`, `(def_ineq)` at `v*`, and `G*` lower
  `(p/4, 2ε)`-regular (via `selfLowerRegular_mono` = LR2 with `α = 1/2`);
  then GKO at `(ν,ε,p) := (3η, 2ε, p/4)` and restriction of the colouring.
  The clean way to formalise this is a separate lemma
  `selfLowerRegular_image` transporting `SelfLowerRegular 𝓖 univ p ε` to the
  image family under `Fin.castSucc` on the vertex set `Set.range Fin.castSucc`
  (using `Finset.preimage` / `Finset.image_preimage`).
**Next targets.**  (a) `GKOStatement` (Theorem 10.8) as a deep input plus
Corollary 10.13 (`cor:optcol`), whose odd case adds a new vertex to `G`
(using `selfLowerRegular_mono` = LR2); (b) §7's absorption lemmas
(`crossing-absorption`, `internal-absorption`, `huge-edge-absorption`,
`difficult-edge-absorption`); note that **Lemma 7.12
(`difficult-edge-absorption`) is self-contained**: it uses only Vizing
(refinement) and Tutte's theorem (available in Mathlib as
`SimpleGraph.tutte` / `IsTutteViolator`), so it is provable without any new
deep input.  (c) §9's nibble (needs Ehard–Glock–Joos).  (d) the
**multi-hypergraph model** (`𝓗'` obtained from `𝓗_small ∖ R_res` by adding
singleton edges): this is the remaining modelling bottleneck for §7, §9,
§11.3 and §12 — a pragmatic model is a set-family of edges of size `≥ 2`
together with a multiplicity function `Fin n → ℕ` for the singleton edges.

## Progress on §10 (COMPLETE) and §7 (this stretch of work)

* **§10 is now COMPLETE.**  `Submission/EFL/OptCol.lean` states Theorem 10.8
  (`thm:optcol`, Glock–Kühn–Osthus) as the deep input `GKOStatement` and
  proves Corollary 10.13 (`cor:optcol`) in the even case
  (`optcol_corollary_even`), together with the reusable *core* form
  `optcol_corollary_core` (which takes the paper's `(def_ineq₂)` inequality
  `2(Δ − δ) ≤ Σ_v (Δ − d(v))` at a minimum-degree vertex instead of the
  hypothesis "at least `Δ` vertices have degree `< Δ`").
  `Submission/EFL/OptColOdd.lean` adds the **odd case**: for odd `n` it builds
  the extended graph on `Fin (n+1)` obtained by joining a new vertex
  `Fin.last n` to `t := ⌊Δ − 2ηn⌋` vertices of degree `< Δ`, and applies
  `optcol_corollary_core` to it.  Contents:
  - `famImage` (the image of a hypergraph under an injective vertex map) and
    `extendVertex 𝓖 T` (add a new vertex);
  - degree bookkeeping `degAt_extendVertex_castSucc`, `degAt_extendVertex_last`,
    `hypergraphDegree_extendVertex_*`, `hypergraphMaxDegree_extendVertex`
    (`Δ(𝓖_ext) = Δ(𝓖)` when `T` consists of non-maximum-degree vertices),
    `degAt_extendVertex_le_max`;
  - edge-count transport `castSuccFinset`, `card_castSuccFinset`,
    `edgeCount_famImage_castSucc`;
  - lower-regularity transport `selfLowerRegular_famImage_castSucc` and
    `selfLowerRegular_extendVertex` (LR2 with `α = 1/2`, i.e.
    `(p,ε) ↦ (p/4, 2ε)`);
  - the headline `optcol_corollary_odd` and the parity-free
    `optcol_corollary` (hypotheses `0 < η`, `0 < ε`, `8ε < p`, `p < 1`,
    `24(η+ε) ≤ p` — slightly stronger than the even case needs, which is what
    the parameter hierarchy in §12 provides).
  This is used in §12's Case 2 (Type A₂) at `p = ρ/4`, `ε = ε^{1/3}`,
  `η = 22ε`.

* **§7 has been started**: `Submission/EFL/Absorption.lean` contains
  - `absorberFam R U` (the family `𝓕(R) = {N_R(u) ∩ U} ∪ {N_R(u) ∖ U}`),
  - `PseudoRandom M 𝓕 γ κ` (Definition `pseudorandom-matching-def`),
  - `AbsorbableByPseudo` / `AbsorbableBySmall` / `AbsorbableByTypical` /
    `Absorbable` (Definition `def:absorbable`, alternatives AB-pseudo,
    AB-med, AB-huge),
  - the matching API `mem_matchVert`, `matchVert_mono`, `subset_matchVert`,
    `matchVert_union`, `isMatching_union`,
  - `exists_matching_covering_of_upperRegular` — Proposition
    `crossing-matching-prop` in the form used by the crossing absorption
    lemma (a `A`/`VN`-parameterised statement with the `B = univ ∖ A`
    complement so that the "`ξ v(H)`" threshold of the commons lemma
    `upper_regular_exists_injective` becomes `ξn`, exactly as in the
    application);
  - `exists_matching_covering_of_greedy` — the greedy/Hall counterpart used
    when `|A|` is small (every `a ∈ A` has strictly more than `|A|`
    neighbours).

  **What remains in §7** (in dependency order; all of it is pure counting on
  top of the two matching propositions above):
  1. *one-step lemma* (`crossing_step`): given the absorbable hypothesis
     `AbsorbableByPseudo 𝓗 N R U ∅ ρ ε γ κ ξ`, a matching `N`, a set `used`
     of already-used edges of `R` with `|used|-degree ≤ κn`, and the numeric
     margins, produce a matching `Nabs ⊆ R ∖ used` covering
     `A = U ∖ V(N)`.  The degree computation is
     `d_{R∖used}(u) ≥ γ|N_R(u) ∖ U| − κn ≥ γ(ρ(99/100 − ε) − 10γ)n − κn`
     (linearity of `𝓗` + Definition `def:typicality` with `X = U`), and
     `|A| ≤ γn/50`, so `d ≥ 2ρ|A|`; when `|A| ≥ ξn/ρ` apply
     `exists_matching_covering_of_upperRegular` (with the upper regularity of
     `R` restricted to `R ∖ used`), otherwise
     `exists_matching_covering_of_greedy` (because
     `d(u) ≥ 96γρn/100 > ξn/ρ > |A|`).
  2. *iteration*: process the indices one at a time in a well-order,
     accumulating `used := ⋃_{t<ℓ} Nabs_t`; formalise by induction on `k`
     for `N : Fin k → Set 𝓗` (`Fin.cases` in the step).  The only data the
     induction needs is `|used|`-degree `≤ κn`, which holds for *any* choice
     of the previous `Nabs` (each is a matching, so it contributes at most
     one edge through each vertex).
  3. *assembly*: `crossing_absorption` with
     `N'_i := N_i ∪ Nabs_i`; perfect coverage of `U` follows from
     `Nabs_i` covering `A_i = U ∖ V(N_i)`.
  Then the same pattern gives `internal_absorption` (Lemma
  `internal-absorption-lemma`, needing the internal matching proposition
  `upper_regular_exists_perfect_matching`, in flight) and
  `huge_edge_absorption` (Lemma `huge-edge-absorption-lemma`, which needs
  both and the `AB-med`/`AB-huge` cases).

  **Design note.**  `internal-matching-prop` must be stated with the paper's
  hypothesis `ξ ≪ ρ` (a fixed small multiple, e.g. `10ξ ≤ ρ`), *not* just
  `ξ ≤ ρ`: with `ξ = ρ` the statement is false (two disjoint cliques
  `K_{m/2} ⊔ K_{m/2}` with `m ≡ 2 (mod 4)` and `ρ = ξ = 1/2` satisfy all the
  numerical hypotheses but have no perfect matching — the trivial bound
  `e(S,T) ≤ |S||T| = (ρ+ξ)|S||T|` is all the regularity gives).  The
  restatement also carries the threshold `B ≤ ρ²m` (needed for the union
  bound in the balanced-bipartition Chernoff argument).

## External deep theorems needed as inputs (formalise or import)

* Vizing's theorem (edge-colour graphs with `Δ+1` colours) — Thm 6.3.
* Kahn's theorem: list-chromatic index of hypergraphs is `Δ + o(Δ)`
  (Thm 6.4) — needed for medium/large edges in the non-extremal regime.
* Lovász `(g,f)`-factor theorem (Thm 6.6).
* Ehard–Glock–Joos pseudorandom matching theorem (Thm 6.2) and the derived
  sparse corollary (Cor 6.1); the engine of every nibble argument.
* Molloy–Reed (Thm 7.2) and Alon–Krivelevich–Sudakov (Thm 7.4) on
  colouring locally sparse graphs, applied to parts of the line graph.
* Glock–Kühn–Osthus (Thm 10.8): optimal edge-colourings of dense
  pseudorandom graphs (derived from the overfull subgraph conjecture work).

None of these currently exists in Mathlib (rev. 6f1ef4e5).  Each is itself a
major formalisation project.  `Submission/EFL/LineGraph.lean` gives the
bridge needed to apply graph-colouring results to the problem.

## How the final proof will plug in

A complete proof should produce (constructively or classically) a term of
type `eflStatementThreshold` — the conjunction of the statements of
`large-edge-thm` (restated for `Fin n`), the three case analyses of §12, and
`BigEdges.lean`'s reduction.  Then `eflStatement_iff_threshold.2` converts it
to `eflStatement`, which is propositionally identical to `theorem_1_1`
(both unfold to the same formula, so `change eflStatement` closes the gap in
`Submission.lean`).

## State of §7 (this stretch of work)

**Lemma `crossing-absorption-lemma` IS PROVED** (`CrossingAbsorption.lean`):
`crossing_absorption` — for `k ≤ κn` edge-disjoint matchings `N_i`, each
`(γ,κ)`-pseudorandom w.r.t. `𝓕(R) ∪ {U, ∅}`, and `|U| ≤ n/100`, there is a
family `N'` with `N_i ⊆ N'_i`, `N'_i ∖ N_i ⊆ R`, edge-disjoint, with perfect
coverage of `U`.  The proof is the paper's: `crossing_step` (one step, from
`crossing_degree`/`crossing_degree_chain` — the estimate
`d_{R∖used}(u) ≥ γ(ρ((1−ε) − 1/100)n − 10γn) − 2κn ≥ 2ρ|A|` — plus
`exists_matching_covering_of_upperRegular` when `|A| ≥ ξn/ρ` and
`exists_matching_covering_of_greedy` otherwise) and the iteration
`crossing_iter` (induction on `k` with `Fin.snoc`, using
`ncard_nbrs_famUnionIdx_le` for the `used`-degree bound).  Margins:
`CrossingMargins` with the arithmetic lemmas `crossing_arith_main`,
`crossing_arith_greedy`.

**Lemma `internal-absorption-lemma` IN PROGRESS**
(`InternalAbsorption.lean`, `InternalStep.lean`).  Already available:
`InternalMatchingInput n B` (the perfect-matching input, i.e. Proposition
`internal-matching-prop`, to be discharged from the commons lemma
`upper_regular_exists_perfectMatching_general`), `degIn` (from
`GFactor.lean`), `internal_degree_chain` (every `u ∈ W` has `≥ 3ρ|W|/4`
available neighbours, where `W` is `U ∖ V(N)` with at most one vertex
deleted), `internal_matching_step` (the matching on such a `W`, with `ξ' =
400ξ/γ`), `famToSet` (matching families as families of edges of `𝓗`),
`restr`/`degIn_restr`, `internal_pair` (the `{u,v}` pair when
`|U| ≤ (1−2ε)n`) and `internal_step_A` (that case of the one step: a matching
of available edges of `R` covering all of `U ∖ V(N)`).

**§7.2 IS COMPLETE (`internal-absorption-lemma`, Lemma 7.2, PROVED).**
`Submission/EFL/InternalStepB.lean` + `Submission/EFL/InternalMain.lean` prove
`internal_absorption`: for `k ≤ κn` edge-disjoint matchings `N_i`, each
`(γ,κ)`-pseudorandom w.r.t. `𝓕(R) ∪ {U,S}`, there are matchings `N'_i ⊇ N_i`
with `N'_i ∖ N_i ⊆ R`, pairwise edge-disjoint, with perfect coverage of `U`
if `|U| ≤ (1-2ε)n` and nearly-perfect coverage with defects in `S` otherwise.
The pieces: the perfect-matching core `internal_matching_of`, the fresh defect
choices `internal_pick_A` / `internal_pick_B`, the one-step lemmas
`internal_step_A2` / `internal_step_B2`, and the iteration `internal_iter`
(generic in the extra conclusion `Extra`, accumulating the used absorber edges
`used` and the injected defect set `P`).
`InternalMargins` (in `InternalAbsorption.lean`) gained the field
`hγn : 4 ≤ γ^2 * n` (the paper's `γ ≫ 1/n`), used to inject the defect
vertices.

**`InternalMatchingInput` IS DISCHARGED** (`internalMatchingInput`, in
`Submission/EFL/Comm/InternalMatchingConnect.lean`): the paper's Proposition
`internal-matching-prop` is now a theorem, obtained by transporting the
*ported* commons lemma `upper_regular_exists_perfectMatching_general`
through the `SimpleGraph ↥W` of a 2-edge family (`graphOf`, with
`graphOf_degree` — the degree is `degIn` — and `upperRegular_graphOf` — the
upper-regularity transfers) and converting a perfect matching back into a
matching family via the involution `f v = the unique neighbour of v`
(`exists_matchingFamily_of_perfectMatching`; `Subgraph.isPerfectMatching_iff`
gives `∀ v, ∃! w, M.Adj v w`, and the orbits `{v, f v}` are automatically
disjoint).
The port (`Submission/EFL/Comm/`, produced with Mathlib's `#min_imports`)
consists of `InternalEdgesUpperRegAvg.lean` and
`UpperRegularPerfectMatching.lean`; both are in the cone.  Note
`Mathlib.Combinatorics.SimpleGraph.Tutte` had to be added by hand to the
`#min_imports` output.

The original plan (kept for reference):

1. `internal_step_B` (`InternalStep.lean`): the case `(1−2ε)n < |U|`, where
   `|S| ≥ γn` and `|S| ≥ n/100`.  Choose a *distinct* defect vertex
   `u ∈ S ∖ V(N)` (distinctness is needed for the nearly-perfect coverage:
   keep a set `P` of previously chosen defects, `|P| ≤ k ≤ κn`, and use
   `|S ∖ V(N)| ≥ γ|S| − κn ≥ γ²n/2 > κn ≥ |P|`, which is what the margin
   `100κ ≤ γ²` is for), then `W := (U ∖ V(N))` if that is even and
   `(U ∖ V(N)) ∖ {u}` otherwise, and a perfect matching of `restr (R ∖ used) W`
   covering all but that one vertex.  No `{u,v}` edge is added.
2. The **iteration** for §7.2: as `crossing_iter`, but with two phases (the
   choice of the defects first — a `Fin k`-indexed iteration accumulating `P`
   and `used` — then the matchings, accumulating `used`).  For case A the
   matching of `internal_step_A` *contains* the `{u,v}` edge, so a single
   iteration over the one-step lemma suffices if the one-step lemma is
   phrased uniformly (with `u ∈ S` in case B and `u` arbitrary in case A);
   the accumulated `used` is the union of `≤ k` matchings, so its degree is
   `≤ k ≤ κn` (use `ncard_nbrs_famUnionIdx_le`).
3. The **assembly** `internal_absorption`: `N'_i := N_i ∪ Nabs_i`; in case
   `|U| ≤ (1−2ε)n` this gives `PerfectCoverage N' U`, otherwise
   `NearlyPerfectCoverage N' U S` (the defect vertices are distinct and lie in
   `S`; `NearlyPerfectCoverage` is in `Reservoir.lean`).
4. Then discharge `InternalMatchingInput` from the commons lemma
   `upper_regular_exists_perfectMatching_general` (via a `SimpleGraph` on the
   subtype `↥W` with `G.Adj x y := ({x.1, y.1} : Set (Fin n)) ∈ R`, converting
   `M.IsPerfectMatching` into an involution `f` with `G.Adj v (f v)` for
   `f v ≠ v` and then into the matching family `{{v, f v}} ⊆ R`).

After §7.2: `huge-edge-absorption-lemma` (§7.3; needs the `AB-med`/`AB-huge`
alternatives of `Absorbable` and both the crossing and internal lemmas) and
`difficult-edge-absorption` (Lemma 7.12, self-contained; the Tutte core is
available as `Commons.Combinatorics.SimpleGraph.exists_perfectMatching_of_minDegree`
— for a graph on an even number of `> 4` vertices with `δ ≥ v − 3` there is a
perfect matching — and `Commons.Combinatorics.SimpleGraph.vizing_two_max`
supplies the Vizing step).

## PLAN FOR §7.3 (`huge-edge-absorption-lemma`, Lemma 7.3)

Statement (paper): `0 < 1/n₀ ≪ ξ ≪ κ ≪ γ ≪ ρ, ε ≪ 1`, `n ≥ n₀`, `k ≤ γn`,
`𝓗` an `n`-vertex linear hypergraph, `G := 𝓗^{(2)}`, `R ⊆ E(G)`,
`U := V_+^{(1-ε)}(G)`, `S ⊆ U` with `|S| > (γ+ε)n` if `|U| > (1-10ε)n`, and
`𝓝 = {N_1,…,N_k}` edge-disjoint matchings such that for each `i` either
(a) `AbsorbableBySmall` or (b) `AbsorbableByTypical` **and** `N_i` is not
difficult.  Conclusion: `N'_i ⊇ N_i`, `N'_i ∖ N_i ⊆ R`, pairwise
edge-disjoint, and perfect coverage of `U` if `|U| ≤ (1-10ε)n`, nearly-perfect
with defects in `S` otherwise.

Pieces to build (all of them new; the existing `internal_*`/`crossing_*`
machinery has the right shape but the wrong hypotheses):

1. Definitions in `Absorption.lean`: `IsDifficult U M` :=
   `2 ≤ (Uᶜ).ncard ∧ 3*(Uᶜ).ncard ≤ 4*(matchVert M ∩ Uᶜ).ncard`, and **fix
   `AbsorbableByTypical`** to match the paper's `AB-huge` (it must include
   `U ∪ matchVert M ∈ 𝓥` and `U ∖ matchVert M ∈ 𝓥` for the *same* `𝓥` as
   `AB1`, and it should NOT contain the `AbsorbableByPseudo` conjunct — the
   current definition is far too strong for §12 and the typicality at
   `U ∪ V(N_ℓ)` in the crossing step is unavailable without it).
2. The **crossing** part: for `|U_ℓ| ≤ n/100`, (`H_ℓ` = the bipartite graph
   between `U_ℓ` and `V_ℓ = (V∖U)∖V(N_ℓ)`), show `d_{H'_ℓ}(u) ≥ ρn/7` for
   `u ∈ U_ℓ` — case (b): `v(N_ℓ) ≤ (3/4+ε)n` (not difficult!) gives
   `|V_ℓ| ≥ n/6` and typicality at `U ∪ V(N_ℓ)` gives
   `d ≥ ρ(n/6−εn) − 10γn`; case (a): `v(N_ℓ) ≤ γn`, `|U| ≤ n/50` and
   typicality at `U` gives `d ≥ (ρ(49/50−ε) − 11γ)n`.  Then apply
   `exists_matching_covering_of_upperRegular` (if `|U_ℓ| ≥ ξn/ρ`) or
   `exists_matching_covering_of_greedy`.
3. The **internal** part for `n/100 < |U_ℓ|`: `d_{G''_ℓ}(u) ≥ 3ρ|U'_ℓ|/4`
   with `G''_ℓ = G_ℓ[U'_ℓ] ∖ ⋃` previous absorbers; case (b)
   `d ≥ ρ(|U_ℓ|−εn) − 11γn − 1`, case (a)
   `d ≥ ρ(|U|−εn) − 12γn − 1`; use `exists_perfectMatching…`/the §7.2
   `internal_matching_of` shape.  The defect vertices `u_ℓ`: distinct, in
   `S` when `|U| > (1-10ε)n` (`|S∖V(N_ℓ)| > γn ≥ k`), and in the small-`|U|`
   case paired with `v_ℓ ∈ N_{G'_ℓ}(u_ℓ) ∖ (U ∪ V(N_ℓ))` (a `{u_ℓ v_ℓ}` edge
   is added when `|U_ℓ|` is odd; there are `> k` candidates).
4. Assembly as in `internal_absorption`: `N'_i := N_i ∪ Nabs_i`, with
   `NearlyPerfectCoverage` for the large-`|U|` case (defects distinct, in S).
   Use `internal_iter` with `Extra u N Nabs := u ∈ S` for the large case.

Note the *ordering*: the paper first builds all crossing absorbers and then
the internal ones; a single iteration over `Fin k` that case-splits on
`|U∖V(N_i)| ≤ n/100` also works, since every estimate only uses "at most `k`
previously used edges".

After §7.3: Lemma 7.12 (`difficult-edge-absorption`), then §11.3, §9, the
multi-hypergraph model and the §12 assembly (see the plan above).

## SESSION NOTE (current stretch)

* §7.2 complete; `InternalMatchingInput` discharged; the ported commons
  perfect-matching lemma is in `Submission/EFL/Comm/`.
* Requested from the fleet: `Commons.Combinatorics.LovaszGFactor.lovasz_gf_factor`
  (Lovász's `(g,f)`-factor theorem, in the form §11 consumes; it would
  discharge `GFactorStatement`).
* Next: §7.3 as planned above (start with the definitions and the crossing
  degree estimates; `IsDifficult`/`AbsorbableByTypical` must be fixed first).
* SESSION NOTE (current stretch, part 3).
  **LEMMA 7.12 (`difficult-edge-absorption`) IS PROVED** in
  `Submission/EFL/DiffAbs.lean` + `Submission/EFL/DiffAbs2.lean` (both
  sorry-free, in the cone):
  * `DiffAbs.lean`: `DiffMargins` (`0 < β`, `β ≤ 1`, `16 ≤ βn`), the degree
    classes `Vdeg 𝓗 d = V^{(d)}(𝓗)` (phrased with
    `{f ∈ 𝓗 | v ∈ f}.ncard` so that the commons lemmas apply directly), the
    pairing constructions `exists_matching_covering_of_pairs` (a complete graph
    on an even set has a perfect matching, via
    `Commons.Combinatorics.Finset.set_pair_partition`) and
    `exists_matching_covering_of_pairs_odd` (pair all but one vertex of an odd
    set and join the last one to an outside partner `y`), and the helper
    `exists_matching_of_perfectMatching` turning a perfect matching of the
    2-graph `graphOf R W` into a matching family `Set 𝓗` whose edges lie in `R`
    and inside `W`.
  * `DiffAbs2.lean`: `disjoint_e_Vdeg` (no vertex of `e` has `𝓗`-degree `n-1`
    or `n-2`), `pairs_of_Vdeg_one`, `notAdj_le_two_of_Vdeg_two`,
    `exists_extension_even`/`exists_extension_odd` (case `U₂ = ∅`),
    `colorable_of_exceptional` (the branch `U₂ = ∅`, `|U₁|` odd,
    `V = e ∪ U₁`: remove a perfect matching of `U₁ ∖ {w}`, then Vizing's
    two-max form for the remaining pair family, then add the fresh colour on
    `{e} ∪ M₁`), `ncard_sub_three_le_degIn` (the min-degree bound on the
    2-shadow induced on `U₁ ∪ U₂`), `exists_extension_of_nonempty_U2` (apply
    `perfectMatching_or_card_le_four`; a perfect matching covers `W` (or
    `W ∖ {u}` for odd order), and in the small case `|W| ≤ 4` resp. `≤ 5` the
    pairing construction of `DiffAbs.lean` covers `U₁` while `|U₂| ≤ 5`), and
    the assembly `difficult_edge_absorption`.
  * COMMONS lemmas requested for this step (all proved by the fleet):
    `Commons.Combinatorics.Hypergraph.{eq_univ_pairs_of_degree,
    ncard_notAdj_le_two_of_degree, huge_edge_disjoint_high_degree}`,
    `Commons.Combinatorics.Finset.set_pair_partition`,
    `Commons.Combinatorics.SimpleGraph.{perfectMatching_or_card_le_four,
    edgeColoring_of_pairFamily_two_max}`.  The last one imports all of Mathlib,
    so it has been PORTED into the cone as `Submission/EFL/Comm/Vizing.lean`,
    `.../VizingTwoMax.lean`, `.../EdgeColoringPairFamily.lean` (the probe
    `#min_imports` reported only the ported `vizing_two_max` as a dependency).
  * LEAN LESSON: `Fintype`/`Decidable` instances are frequently *not* matched
    across two elaborations of "the same" term.  In particular a term of the
    form `Fintype.card ↥W` with `W` a local `set`-definition can be elaborated
    with `Set.fintypeUnion` (after unfolding `W`) in one place and with
    `Subtype.fintype` in another; local `haveI` instances do NOT repair this.
    The robust cure is to phrase helper lemmas without the instance-bearing
    term (`W.ncard`, `degIn R W v`) and to introduce the instance-sensitive
    `SimpleGraph.degree` only once, at the point of use, via
    `rw [graphOf_degree, fintype_card_coe]`.
  * NEXT: §11.3 (`lem:degree-lemma`, needs the multi-hypergraph model), §9
    (EGJ + embed/nibble2/leftover), the multi-hypergraph model and the §12
    assembly.

* SESSION NOTE (current stretch, part 2).
  (a) The Lovász `(g,f)`-factor chain is PORTED into the cone:
  `Submission/EFL/Comm/{BarrierCountGF,AltWalkFlipDegree,GfFactorOfTight,
  GfFactorTight,LovaszGfFactorNat,LovaszGfFactor}.lean`, and
  `Submission/EFL/GFactorDischarge.lean` proves
  **`gfactorStatement : GFactorStatement`** — the deep input of §11.3 is now a
  theorem (callers of `exists_regularising_reservoir` should pass
  `gfactorStatement` instead of a hypothesis).
  (b) §7.3 is about half-way: `Submission/EFL/HugeStep.lean` contains
  `HugeMargins` (the margins `1000γ ≤ ρε`, `1000ε ≤ 1`, `2000 ≤ γρn`,
  `4000ξ ≤ γρ`), the elementary `ncard` lemmas, the crossing degree bounds
  (`huge_cross_degree_a`, `huge_cross_degree_b`, `huge_cross_degree`), the
  crossing step `huge_cross_step` (matching covering `U ∖ V(N)` when
  `|U ∖ V(N)| ≤ n/100`), the internal degree bound `huge_internal_degree` and
  the internal matching `huge_internal_matching` (on an even `W` with
  `(U∖V(N)) ⊆ W ∪ {u}`).
  STILL TO DO in §7.3: the partner choice `huge_pair` (the `{u_i v_i}` edge in
  the small-`|U|` case, `v ∉ U ∪ V(N)`, using not-difficulty + typicality at
  `U ∪ V(N)`), the two internal steps (`huge_internal_step_small` covering all
  of `U ∖ V(N)` with the partner edge when `|U ∖ V(N)|` is odd;
  `huge_internal_step_large` producing the distinct defect `u ∈ S ∖ V(N)`), the
  two iterations (`huge_iter_cov` with no defects, `huge_iter_defect` with
  distinct defects, mirroring `internal_iter`) and the assembly
  `huge_edge_absorption`.
  NUMERIC SUBLEMMAS for §7.3 are proved in the commons by the fleet:
  `Commons.Combinatorics.EFLArith.{crossing_arith_a,crossing_arith_b,
  internal_arith,sixth_arith}` (all with minimal Mathlib imports, safe to
  import into the cone).
  LEAN LESSON (important): a `Finset.filter` whose predicate mentions a
  *defined* family `R' := R ∖ used` (via `set`) gets its `DecidablePred`
  instance by unfolding, which does not match the instance stored in an
  already-compiled lemma's statement (where the family is an abstract
  variable).  The cure is to pass the family as an *argument* of the lemma
  (`{R' : Hypergraph (Fin n)}` with a hypothesis `hR' : R' = R ∖ used`), as in
  `crossing_step_aux` and `huge_cross_step`.
* SESSION NOTE (current stretch, part 4) -- **§11.3 (`lem:degree-lemma`, the
  Regularising Lemma) IS PROVED**, and the first half of Claim 12.1
  (`claim:easyobs`) is in place.
  NEW MODULES (all sorry-free, in the cone):
  * `MultiHypergraph.lean` -- the model of a *linear multi-hypergraph*:
    `MultiHypergraph n = (edges : Set (Set (Fin n)), singles : Fin n → ℕ)`
    with `deg`, `IsLinear`, componentwise `≤`, `ofHypergraph`,
    `regHypergraph` (Definition 11.4: `𝓗` plus `max 0 (n-3-d_𝓗(w))` singletons
    at `w`) and `addSingletons` (the `𝓗'` of Lemma 11.3, whose degree at `w`
    is `max k (d_𝓕 w)`).  Also `sdiff` and `supp`.
  * `DegreeBounds.lean` -- `hdeg`, `hdeg_sdiff`, `hdeg_union`,
    `hdeg_eq_degAt` (for a family of 2-element sets the number of edges
    through `w` equals `|N_R(w)|`; proved by `Set.ncard_congr`),
    `notMem_nbrs_self`, `degAt_le_pred`, and `hdeg_eq_small_add` (splitting a
    degree into the edges of size `≤ r₁` and the rest).
  * `ReservoirType.lean` -- Definition 11.2: `IsReservoirTypeA1`,
    `IsReservoirTypeA2`, `IsReservoirTypeB`, each including the subset
    condition `R_res ⊆ E(G)` (or `⊆ E(G')`), plus
    `degAt_incidentTwo_eq` (for `w ∈ U` the `G'`-neighbourhood is the
    `G`-neighbourhood).
  * `DegreeLemma.lean` -- `DegreeMargins` (the numeric hierarchy actually
    needed: `ρ ≤ 1/2`, `2ρ(n-1) + 1 ≤ εn` for Type `B`, `8ξ ≤ β`,
    `16 ≤ βr₁`, `24 ≤ βn`, `βn/2 ≤ (1-ρ)(n-1)`), `absorber_degAt_abs`
    (the two-sided degree estimate from typicality at `V(𝓗)`), the two
    estimates `hdeg_sdiff_le_A` (Types `A₁`/`A₂`) and `hdeg_sdiff_le_B`
    (Type `B`, splitting on `w ∈ U`) giving
    `d_{𝓗∖R_res}(w) ≤ (1-ρ)(n-1) + ξn`, and the CORE THEOREM
    `regularising_lemma_core` taking the two numerical inputs
    `hE1 : d_{𝓗∖E(G)}(w) ≤ (n-1-d_G(w))/2` and
    `hsmall : d_𝓗(w) - d_{𝓗_small}(w) ≤ 2n/r₁`, producing
    `k := ⌊(1-ρ)(n-1) - βn/2⌋` and `𝓗' := 𝓗_small ∖ R_res` with `k - d(w)`
    singletons at every vertex with `d(w) < k`, together with `𝓗' ⊆ 𝓗_reg`
    and `d_{𝓗'}(w) = (1-ρ)(n-1 ± βn)`.
  * `Regularising.lean` -- **Lemma 11.3 IN FULL** (`regularising_lemma`):
    discharges `hE1` (`hdeg_sdiff_pow2_le`) and `hsmall`
    (`hdeg_sub_small_le`) from the three commons lemmas
    `Commons.Combinatorics.Hypergraph.{card_size_ge_three_mul_two_le,
    card_size_gt_mul_le, card_two_edges_eq_card_nbrs}` (proved by the fleet
    this session).  NUMERIC LEAN LESSONS: (i) do all the arithmetic in `ℝ`
    (cast the `ℕ`-degree bounds) -- `Nat`-subtractions in goals are a trap;
    (ii) pass `Nat.cast_sub`/`Nat.cast_add` explicitly to `rw`; (iii) `omega`
    cannot see a hypothesis whose type is a *set membership* -- extract the
    conjunct first.
  * `EasyObs.lean` -- **Claim 12.1 (EP4) IS PROVED** (`easyObs_EP4`): in a
    Type A colouring of the medium and large edges there is at most one
    colour class that contains a huge edge and is difficult.  The proof uses
    `classVertices_eq_of_colorClass_singleton` (a colour class consisting of a
    single edge covers exactly that edge) and the linearity of `𝓗`: two
    distinct difficult huge colour classes would give two edges meeting in
    ≥ 2 vertices.  The integrality step (`A + B - N ≥ 2` from
    `3N ≤ 4A`, `3N ≤ 4B`, `A, B ≤ N`) is done by splitting on `N ≤ 3`.
    Also **EP3, second part** (`easyObs_EP3_no_difficult`): a Type B colouring
    has no difficult colour class (the class-vertex bounds of the extremal
    alternative are all `≤ δn`, contradicting the `3|V∖U|/4 ≤ δn` that
    difficulty forces once `|V∖U| ≥ (1-2δ)n` and `δ < 3/10`).
  * ALREADY AVAILABLE (earlier sessions, re-used here): `Obs12.lean` proves
    **EP1** (`edgeSize_le_of_meets_Vplus`) and `MainThm2.lean` proves
    **EP2** (`card_largeEdges_meeting_le`).
  * `VplusBound.lean` -- **Claim 12.1 (EP3), first part IS PROVED** in the
    cone: `card_Vplus_le_of_extremal` (also in the `easyObs_EP3_card_Vplus`
    wrapper of `EasyObs.lean`) gives `|V_+^{(1-ε)}(G)| ≤ 2δn` from the volume
    condition `∑_{e ∈ W}|e|(|e|-1) ≥ (1-δ)n(n-1)` on a family `W` of edges of
    size ≥ 3.  Ingredients: the handshake identity
    `sum_degAt_eq_sum_ncard` (`∑_w d_G(w) = ∑_{e ∈ G}|e|`, via `Finset.sum_comm`
    and `Finset.card_filter`) and `sum_degAt_le_two_mul_card`.  The wrapper
    `easyObs_EP3` combines this with EP3's second part: in the Type B case
    `|U| ≤ 2δn` and no colour class is difficult.  (The fleet lemma
    `Commons.Combinatorics.Hypergraph.card_Vplus_le_of_extremal` was requested
    but not needed.)
  * `EGJ.lean` -- the Ehard--Glock--Joos theorem `thm:egj` and its sparsified
    corollary `cor:sparse_egj` are now recorded as `EGJStatement` /
    `SparseEGJStatement` (with `degreeSum`), the input statements §8 rests on.
  NEXT: (i) EP3, first part (`|U| ≤ 2δn` for Type B) -- requested from the
    fleet as `Commons.Combinatorics.Hypergraph.card_Vplus_le_of_extremal`;
    (ii) §12 step 3 (the colour sets `C_med`/`C_diff`/`C_huge`/`C_main`/
    `C_buff`/`C_final` and observations T1/T2); (iii) §9 (EGJ as a `Prop`,
    `lem:embed`, the Nibble Lemma `lem:pseudorandom_matching` and
    `lem:nibble2`) and the residue of the multi-hypergraph model it needs;
    (iv) the §12 assembly and `eflStatement`.
* SESSION NOTE (current stretch, part 5) -- **§12 STEP 3 IS PROVED**, and
  Observation `obs:del_absorber` is in the cone.
  NEW MODULE `Submission/EFL/S12Setup.lean` (in the cone):
  * `IsDifficultSet U X` is the vertex-set form of Definition `defn:difficult`
    (`IsDifficult U M ↔ IsDifficultSet U (matchVert M)`), so that "colour class
    `c` is difficult" can be written without a family argument;
  * the colour sets `Hypergraph.Coloring.hugeColourSet β` (`φ(𝓗_huge)`),
    `...largeColourSet r₀` (`φ(𝓗_large)`) and `...diffColourSet Cmed U β`
    (= the colours of `φ(𝓗_huge) ∖ C_med` whose class is difficult), with the
    membership lemmas `Hypergraph.Coloring.mem_hugeColourSet` (equivalent to
    `φ.AssignedToHuge β`), `...mem_largeColourSet`, `...mem_diffColourSet`
    (NOTE: `mem_hugeColourSet` had to be pushed into the
    `Hypergraph.Coloring` namespace because `Submission/EFL/LargeEdgeCase2.lean`
    already declares a (different) `mem_hugeColourSet`);
  * `card_hugeColourSet_le` (`|φ(𝓗_huge)| ≤ e(𝓗_huge)`, by the injective map
    `e ↦ φ.labels e` from `𝓗.hugeEdges β` -- valid when
    `𝓗.hugeEdges β ⊆ medLarge 𝓗 r₁`, i.e. `r₁ < βn/4`), and
    `card_med_diff_huge_le` (`|C_med ∪ C_diff ∪ C_huge| ≤ |C_med| + e(𝓗_huge)`);
  * `card_diffColourSet_le_one_of_typeA` (Claim 12.1 (EP4)) and
    `..._of_typeB` (Claim 12.1 (EP3), needs `U = Vplus 𝓗 (1-ε)`);
  * the generic finset lemmas `exists_subset_card_max_inter` and
    `subset_of_subset_card_max_inter` (a `D`-element subset of `S` maximising
    `|t ∩ A|` contains `A` when `A ⊆ S`, `|A| ≤ D`);
  * the parameters `Dparam n ρ = ⌊(1-ρ)(n-1)⌋` and
    `D'param D γ = ⌊10γ^{1/2}D⌋`;
  * **`structure IsS12Colours`** (a `Prop`-valued structure whose *data* --
    the seven colour sets -- are parameters, so that it can be constructed by
    `obtain` from the `∃`-valued Type-A/Type-B data): the fields are
    `|C_med| ≤ γn`, `φ(𝓗_med) ⊆ C_med`, `|V({c})| ≤ γn` for `c ∈ C_med`,
    `C_diff ⊆ φ(𝓗_huge)`, `C_diff ∩ C_med = ∅`, `|C_diff| ≤ 1`, the elements
    of `C_diff` are difficult, `C_huge = φ(𝓗_huge) ∖ (C_med ∪ C_diff)`,
    `C_large = φ(𝓗_large) ∖ (C_med ∪ C_diff ∪ C_huge)`, `|C_main| = D`,
    `C_main ⊆ (C_med ∪ C_diff ∪ C_huge)ᶜ`, the *maximality* of `C_main`,
    `|C_buff| = D'`, `C_buff ⊆ (C_med ∪ C_diff ∪ C_huge ∪ C_main)ᶜ`, and
    `C_final = [n] ∖ (C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff)`;
  * **`exists_S12Colours_typeA`** and **`exists_S12Colours_typeB`**: from a
    Type-A (resp. Type-B) colouring `φ` of the medium and large edges, the
    numerical hypotheses `r₁ < βn/4`, `8 ≤ βn`, `n ≥ 1`, `γ₁ ≤ γ` and
    `D + D' + 2γn + 32/β² ≤ n`, one builds the seven sets (the Type-B version
    takes `U = Vplus 𝓗 (1-ε)`);
  * DERIVED: `IsS12Colours.labels_mem` (every medium/large colour lies in
    `C_med ∪ C_diff ∪ C_huge ∪ C_large`), `IsS12Colours.clarge_subset_cmain`
    (from the maximality, when `|C_large| ≤ D`),
    `IsS12Colours.notMem_of_buff_union_final`,
    **`IsS12Colours.class_eq_empty_of_buff_union_final`** (T1),
    **`IsS12Colours.large_nonhuge_of_buff_union_final`** (T2),
    `IsS12Colours.classVertexCount_le_of_buff_union_final` (T2 +
    (6.7:b)(iii) give `|V(φ⁻¹(c))| ≤ βn`), **`IsS12Colours.card_final_ge`**
    (`(ρ - 15γ^{1/2})n ≤ |C_final|` from `|C_med ∪ C_diff ∪ C_huge| ≤ 5γ^{1/2}n`,
    `0 < ρ ≤ 1`, `n ≥ 1`), and **`IsS12Colours.huge_class_inter_U_le`**
    (Type A, `c ∈ C_huge` ⟹ `|V(φ⁻¹(c)) ∩ U| ≤ εn` via EP1).
  NEW MODULE `Submission/EFL/AbsorberDeletion.lean` (in the cone): the paper's
  Observation `obs:del_absorber` -- `IsAbsorber.mono_gamma` (increasing `γ`)
  and **`IsAbsorber.delete`** (`R' ⊆ R` and `Δ(R∖R') ≤ αn` ⟹ `R'` is a
  `(ρ, γ+α, ξ, ε)`-absorber), with `nbrs_eq_union_sdiff`.  This is what Steps
  4--6 use when they delete the matchings of `𝓜_diff`, `𝓜_hm`, `𝓜_main` from
  the absorber `R_abs`.
  FLEET (proved and committed to the commons this session):
  `Commons.Combinatorics.Finset.exists_superset_card_eq` (extend `A ⊆ S` to a
  subset of `S` of size `m`) and
  `Commons.Combinatorics.Finset.exists_fiber_card_ge_div` (partition a finset
  into `t` parts of size `≥ ⌊|s|/t⌋`, for Lemma `lem:leftover`);
  `Commons.Combinatorics.Set.ncard_biUnion_le` requested.
  LEAN LESSONS (important):
  (a) a `structure ... : Prop` may only have *proof* fields -- to bundle data
      (here the seven colour sets) make the structure a `Type` (and then it
      cannot be built by `obtain` from a `Prop`-valued `∃`, because of
      `Prop`-elimination restrictions: `theorem` with a `Type` result fails and
      `Exists.casesOn` is not allowed).  The workable pattern is: a `Prop`
      *predicate* whose parameters are the data (`IsS12Colours ... Cmed Cdiff
      ...`), proved to be inhabited by an `∃`-valued `theorem`.
  (b) `obtain ⟨...⟩ := h` *clears* `h`; save `have hA' := hA` first if `hA`
      is needed inside the structure literal.
  (c) `Set.eq_empty_iff_forall_not_mem` does not exist: use
      `rw [← Set.not_nonempty_iff_eq_empty]` and `rintro ⟨x, hx⟩` (for both
      `Set` and `Finset`).
  (d) in this context `Set.ncard_union_eq`, `Set.ncard_le_ncard` and
      `Set.ncard_inter_le_ncard_left` need the `Finite` argument explicitly
      (`Set.toFinite _`), and `ncard_inter_le_ncard_left s t` bounds
      `(s ∩ t).ncard ≤ s.ncard` -- to bound `(X ∩ N).ncard ≤ N.ncard` use
      `Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)`.
  (e) `abs` hypotheses must be broken with `rw [abs_le] at h` before `linarith`.
  (f) `Finset.mem_union_left (t) (h : a ∈ s) : a ∈ s ∪ t` (the explicit
      argument is the *second* set); the associativity of
      `Cmed ∪ Cdiff ∪ Chuge ∪ Cmain` is left-nested.
  NEXT: (i) §12 Step 4 (apply `difficult_edge_absorption` to the (at most one)
  colour of `C_diff`, define `R_1 = R_abs ∖ ⋃ M_c`, `S_1 = S ∖ ⋃(V^{(n-2)} ∖
  V(M_c))`, and use `IsAbsorber.delete` for `(eq:R1abs)`, `(eq:boundS1)`);
  (ii) §12 Step 5 (apply `huge_edge_absorption` to `{φ⁻¹(c) : c ∈ C_huge ∪
  C_med}` with `R_1`, `S_1`, using `IsS12Colours.huge_class_inter_U_le` and
  `hCmed_vertex` for the absorbability alternatives), then Steps 6--10;
  (iii) §9/§8 (`lem:embed` as a `Prop` input, the Nibble Lemma and
  `lem:nibble2`/`lem:leftover`, all of whose interfaces still have to be
  written down).
* SESSION NOTE (part 6) -- **§12 STEPS 4 AND 5 ARE PROVED**, and
  `NearlyPerfectCoverage` was strengthened to the paper's definition.
  NEW MODULE `Submission/EFL/S12Step4.lean` (in the cone):
  * `subFam S` (the family of edges of `𝓗` corresponding to a family `S` of a
    subhypergraph `𝓖 ⊆ 𝓗`), `mem_subFam`, `IsMatching.subFam`,
    `subFam_singleton`;
  * `ncard_nbrs_famOf_le_one` (`degAt (famOf M) v ≤ 1` for a matching `M`) and
    `IsAbsorber.delete_famOf` (Observation `obs:del_absorber` specialised to
    deleting a single matching: the deleted part has max degree at most 1, so
    `γ` increases by `1/n`);
  * `famUnionIdx_if_le_one` (`famUnionIdx` of a family indexed by a colour set
    containing `c₀` with `∅` off it is `famOf M`),
    `ncard_biUnion_defect_le_five`;
  * **`s12_step4`**: for `C_diff` of `IsS12Colours` (Type A, SingletonClasses
    for huge), either `𝓗.chromaticIndex ≤ n` or there are `Mdiff : Fin n →
    Set 𝓗`, `R₁`, `S₁` with `Mdiff = ∅` off `C_diff`; `subFam (φ⁻¹(c)) ⊆
    Mdiff c`; `Mdiff c ∖ φ⁻¹(c) ⊆ 𝓗.pow2`; `IsMatching`; `Covers (V^{(n-1)})`;
    `|V^{(n-2)} ∖ V(M_c)| ≤ 5`; `R₁ = R_abs ∖ famUnionIdx Mdiff`;
    `S₁ = S ∖ ⋃_{c ∈ C_diff}(V^{(n-2)} ∖ V(M_c))`; `S₁ ⊆ S`;
    `R₁` is a `(ρ_abs, 3γ/2, ξ, ε)`-absorber; and `|S| - 5 ≤ |S₁|`
    (the paper's D1 + `(eq:R1abs)` + `(eq:boundS1)`).
  NEW MODULE `Submission/EFL/S12Step5.lean` (in the cone):
  * `colourFam φ c` (the colour class `c` of `φ` as a family of edges of `𝓗`),
    `mem_colourFam`, `matchVert_colourFam` (`V(φ⁻¹(c)) = φ.classVertices c`),
    `disjoint_colourFam`, `isMatching_colourFam`;
  * `colourEnum s`, `colourEnum_mem/_injective/_symm` (the enumeration
    `Fin s.card ≃o ↥s` of a colour set, from `Finset.orderIsoOfFin`);
  * **`s12_step5`**: applies `huge_edge_absorption` (Lemma 7.3, with `3γ/2`
    playing the role of `γ`) to the huge and medium colour classes and returns
    `Mhm : Fin n → Set 𝓗` with HM1 (`Mhm c ⊇ colourFam φ c`, added edges in
    `R₁`), HM2 (perfect coverage of `U` if `|U| ≤ (1-10ε)n`, nearly-perfect
    coverage with defects in `S₁` otherwise, including the new clause
    `|U ∖ V(M_c)| ≤ 1`).  The absorbability of the colour classes is *verified
    inside* from the absorber `R₁`, the collection `𝓥`, the size bounds
    `|V(φ⁻¹(c)) ∩ U| ≤ εn` (huge) and `|V(φ⁻¹(c))| ≤ (3γ/2)n` (medium), and
    non-difficulty of the huge classes.
  OTHER CHANGES:
  * `Reservoir.lean`: `NearlyPerfectCoverage` now also records
    `∀ i, (U ∖ V(N_i)).ncard ≤ 1` (the paper's definition, item (ii));
    `InternalMain.lean` (`internal_absorption`) and `HugeStep2.lean`
    (`huge_edge_absorption`) were updated accordingly (both already had the
    `hmiss` fact).
  * `S12Setup.lean`: `IsS12Colours` gained the field
    **`hCdiff_full`** (`c ∈ φ(𝓗_huge)`, `c ∉ C_med`, `φ⁻¹(c)` difficult ⟹
    `c ∈ C_diff`), i.e. `C_diff` is the *full* set of difficult huge colours;
    this is what supplies `¬ IsDifficult U (φ⁻¹(c))` for `c ∈ C_huge`
    (needed by Step 5).
  NEXT: (i) write the deep inputs of §8/§9 as `Prop`s in a new module
  `Submission/EFL/Nibble.lean` — the Nibble Lemma `lem:nibble2` and the
  Leftover Lemma `lem:leftover` (the paper's C1--C4 / L1--L5 and N1--N3 /
  F1--F2), plus `lem:embed`; they need a matching notion for
  `MultiHypergraph` (singleton multiplicities) — the intended encoding is a
  family `Set (Set (Fin n))` together with `⊆ 𝓜.edges ∪ {{v} | 1 ≤ 𝓜.singles v}`
  and pairwise disjointness;
  (ii) then §12 Step 6 (apply `lem:nibble2` to `C_main`, using
  `regularising_lemma` for `𝓗'` and `𝓗* = 𝓗' ∖ ⋃_{c ∈ C_diff} M_c`), Step 7
  (apply `lem:leftover` to `C_buff`), Steps 8--10 and the assembly.
* SESSION NOTE (part 7) -- the deep §8/§9 inputs are now recorded as `Prop`s
  and the structural part of §12 Step 8 is proved.
  NEW MODULE `Submission/EFL/Nibble.lean` (in the cone):
  * `MultiHypergraph.edgeSet` (the proper edges plus the singleton `{v}` at
    every vertex with positive singleton multiplicity) and
    `MultiHypergraph.IsMatching` (a family of pairwise disjoint vertex sets
    all of which lie in `edgeSet`; the singleton multiplicities are collapsed,
    so a matching uses at most one `{v}`); `MultiHypergraph.pow2` (`𝓗^{(2)}`);
  * the vertex-set vocabulary `VplusTwo` (`V_+^{(x)}(G)` for a 2-graph `G`),
    `famVert` (`⋃₀ N`), `CoversFamMulti`, `NearlyPerfectCoverageFam`,
    `nonsing` (`{e ∈ N | 2 ≤ |e|}`) and `EdgeDisjointFam` (two families are
    edge-disjoint when their *proper* parts are disjoint: singleton edges
    exist in several copies in a multi-hypergraph, so two matchings may each
    use a `{v}`);
  * the glue between `Set (Set (Fin n))` and `Set 𝓗`:
    `isMatching_toFam`/`IsMatching.toFam` (a pairwise disjoint family of
    vertex sets whose proper members are edges of `𝓗` becomes a matching of
    `𝓗` after deleting its singletons), `IsMatching.famOf`
    (`famOf M` of a matching `M` of `𝓗` is a matching of
    `ofHypergraph 𝓗`), `edgeSet_ofHypergraph`,
    `MultiHypergraph.isMatching_famOf`, `famVert_famOf`,
    `coversFamMulti_famOf`;
  * **`NibbleStatement`** (= Lemma `lem:nibble2`) and
    **`LeftoverStatement`** (= Lemma `lem:leftover`), stated exactly with the
    paper's hypotheses C1--C4 / L1--L5 and conclusions N1--N3 / F1--F2, all in
    terms of the above vocabulary.  These are the deep inputs of §7 Steps 6--7;
    the paper proves `lem:nibble2` from `SparseEGJStatement` plus `lem:embed`
    and `lem:pseudorandom_matching`, and `lem:leftover` from Kahn's theorem
    plus `huge_edge_absorption`.
  NEW MODULE `Submission/EFL/S12Step8.lean` (in the cone):
  * **`s12_h_final_decomposition`** (`eqn:h_final`): if `𝓜_prev` contains every
    colour class of `C_prev = C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff`, only
    adds small edges (`(hexc)`), and covers all small edges outside `R_res`
    (`(hcover)`, from B1), then every edge of `𝓗` lies in `𝓜_prev`, in
    `R_final = R_res ∖ ⋃𝓜_prev`, or in a colour class of `C_final`.
  * **`s12_deg_h_final`** (`eqn:deg_h_final`):
    `d_{𝓗_final}(w) ≤ |C_final| + m(w) - min(n - d_𝓗(w), 3)` for
    `𝓗_final = 𝓗 ∖ ⋃_i M_i` with `|ι| = n - |C_final|` edge-disjoint
    matchings `M_i` of the regularised multi-hypergraph (the hypothesis
    `hsingle` bounds the number of `M_i` covering `w` only by a singleton edge
    by `n - 3 - d_𝓗(w)`, which is what the multi-hypergraph edge-disjointness
    provides in the paper).
  ALSO IN `Nibble.lean`: the degree arithmetic for Step 6 --
  `MultiHypergraph.hdeg_sdiff_add` (`hdeg (𝓜.edges ∖ 𝓕) w + hdeg 𝓕 w =
  hdeg 𝓜.edges w` for `𝓕 ⊆ 𝓜.edges`), `deg_sdiff_le`, `deg_sdiff_ge`
  (`𝓜.deg w - 1 ≤ (𝓜.sdiff 𝓕).deg w` when `hdeg 𝓕 w ≤ 1`),
  `hdeg_le_one_of_pairwise_disjoint`, `hdeg_famOf_le_one` (a single matching
  has degree at most one at each vertex -- NOTE: this is *false* for
  `famUnionIdx` of several matchings, which is why Step 4's `C_diff` having at
  most one element matters), and `abs_deg_sdiff_sub_le`
  (`|d_{𝓜∖𝓕}(w) - D| ≤ C + 1 + |(1-ρ)(n-1) - D|` when
  `|d_𝓜(w) - (1-ρ)(n-1)| ≤ C` and `hdeg 𝓕 w ≤ 1`).
  NEW MODULE `Submission/EFL/S12Step6Aux.lean` (in the cone): the
  self-contained estimates for checking the hypotheses of `NibbleStatement` in
  Step 6 -- `Dparam_floor_bound` (`|(1-ρ)(n-1) - D| ≤ 1`),
  `s12_star_degree` (C3: `|d_{𝓗*}(w) - D| ≤ 2βD` for
  `𝓗* = 𝓗'.sdiff 𝓕`), `s12_C1_slack` (C1: `D + γn ≤ |S₂|` from
  `D + 4εn ≤ |S₂|`, needs `0 ≤ ε`), `s12_C4_small`
  (C4: `|V(M_c)| ≤ βn ≤ 2βD` from `n ≤ 2D`).
  NEXT: (i) the conversion of Steps 3--5 data into the inputs of
  `NibbleStatement` and the proof of **Step 6** (`𝓗'` from `regularising_lemma`
  with `β/2`, `𝓗* = 𝓗'.sdiff (famUnionIdx Mdiff)`, degrees
  `d_{𝓗*}(w) = (1±2β)D`, C1 `|S₂| ≥ D + 4εn`, C4 from EP2 and
  `|V(φ⁻¹(c))| ≤ βn`), then **Step 7** (`LeftoverStatement` with `C_buff`,
  `𝓗_rem`), defining `R₃`/`S₃` and their bounds;
  (ii) **Step 9** (the `m(w)` bounds `mbound_1`--`mbound_3` and UC1--UC4, which
  rest on `s12_deg_h_final` and the near-perfect coverage data of
  `𝓜_hm`/`𝓜_main*`/`𝓜_buff`);
  (iii) **Step 10** and the assembly: Case A₁ = Vizing on `G_final`, Case A₂ =
  Corollary 10.13 (`OptCol.lean`), Case B = `hall_based_finishing`
  (Lemma 10.2), producing `𝓜_final` and hence `𝓗.chromaticIndex ≤ n`; then the
  `∀ᶠ n`/`eflStatementThreshold` wrapper and `theorem_1_1`.
* SESSION NOTE (current stretch, part 8) -- **§12 STEPS 6 AND 7 ARE PROVED**.
  NEW MODULE `Submission/EFL/S12Step6.lean` (in the cone, ~700 lines):
  * `famUnionFinset M C` -- the union of a family of matchings indexed by a
    finset of colours (`mem_famUnionFinset`, `famUnionFinset_insert`,
    `famUnionFinset_singleton`, `famUnionFinset_mono`), and
    `hdeg_famUnionFinset_le_one` (a family of matchings supported on at most
    one colour has degree at most one at every vertex).
  * `MultiHypergraph.edgeSet_mono`, `MultiHypergraph.IsMatching.mono`
    (monotonicity for the componentwise order) and `isMatching_famOf_reg`
    (`famOf M` is a matching of `𝓗_reg` when `M` is a matching of `𝓗`).
  * the bridges `VplusTwo_pow2_reg` (`𝓗_reg^{(2)} = 𝓗^{(2)}`) and
    `incidentTwo_pow2_reg` -- note that `incidentTwo X U` of an *already*
    2-uniform `X` introduces a redundant `edgeSize e = 2` conjunct, so these
    lemmas are NOT `rfl` and must be applied by `rw`.
  * `IsS12Colours.large_of_mem_cmain` (every edge of a colour class of
    `C_main` is large), `IsS12Colours.classVertexCount_le_of_mem_cmain`
    (`|V(φ⁻¹(c))| ≤ βn` for `c ∈ C_main`, from the shared `(6.7)(iii)` field)
    and `card_cmain_meeting_le` (Claim 12.1 (EP2) for the colours of `C_main`).
  * `S12Step6Result` -- a `Prop`-valued predicate (the data `𝓗'`, `𝓗*`, `N_c`,
    `M_c` are its `∃`-witnesses) collecting the paper's N1--N3 and MA1/MA2
    together with `(eq:R3abs)` (`R₃ = R₂ ∖ ⋃_c N_c` is a
    `(ρ_abs, 4γ, ξ, ε)`-absorber) and `(eq:boundS3)`.
  * **`s12_step6`** proves it: the regularising lemma (with `β/2`) gives `𝓗'`,
    `𝓗* = 𝓗' ∖ 𝓕` (where `𝓕 = ⋃𝓜_diff`) has degrees `(1 ± 2β)D`
    (`s12_star_degree`), the Nibble Lemma is applied with `D := C_main.card`
    (see below), the singleton edges of `N_c` are deleted (`toFam`) to obtain
    `𝓜_main`, and `(eq:R3abs)` follows from `IsAbsorber.delete` with the
    `R₂`-version of N2.
  CHANGES to `Nibble.lean`:
  * `NibbleStatement` is now indexed by `Fin D` instead of `{V : Type*}
    [Fintype V]`: a `{V : Type*}` binder cannot be instantiated at `Fin k`
    (Lean refuses to unify `Type 0` with the universe metavariable), and the
    paper indexes `𝓜 = {M_1, …, M_D}` by `[D]` anyway.
  * `LeftoverStatement` is likewise indexed by `Fin k` (with `γD/2 ≤ k ≤ γD`
    in place of the colour-set cardinality), its L4's degree hypothesis is
    the *hypergraph* degree `MultiHypergraph.hdeg 𝓗rem v` (not `degAt`, which
    only counts 2-edges), and the hypothesis `V(𝓗) = V(𝓗_rem)` has been
    dropped (the paper's proof of `lem:leftover` never uses it).
  NEW MODULE `Submission/EFL/S12Step7.lean` (in the cone, ~450 lines):
  * `Typical.mono_set`/`IsAbsorber.mono_set` (monotonicity in `𝓥`),
    `degAt_le_hdeg`, `disjoint_famOf`, `famOf_toFam`
    (`famOf (toFam G) = {e | e ∈ 𝓗 ∧ e ∈ nonsing G}`), `mem_toFam_iff`,
    `VplusTwo_pow2_ofHypergraph`/`incidentTwo_pow2_ofHypergraph` (the same
    bridges for `ofHypergraph 𝓗`), `matchVert_toFam`
    (`matchVert (toFam G) = famVert G` for a subfamily of a hypergraph
    without singletons) and `card_colours_meeting_le` (Claim 12.1 (EP2) for an
    arbitrary colour set of large colours).
  * `S12Step7Result` -- the matchings `𝓜_buff` with `(B1)` and `(B2)`, and
    **`s12_step7`** proving it: the Leftover Lemma is applied with the ambient
    multi-hypergraph `ofHypergraph 𝓗` (no singleton edges at all in Step 7),
    `D := C_main.card`, `k := C_buff.card` and `γ := 10√γ`; the hypotheses
    L1--L5 are verified from `IsS12Colours`'s T2 field, MA2(ii) of Step 6
    (the `Δ(𝓗_rem) ≤ 2γD` bound) and EP2.
  LEAN LESSONS (new):
  (a) A theorem's `{V : Type*}` binder cannot be instantiated at `Fin k`
      ("`Fin k` has sort `Type` but is expected to have type `Type u_1`").
      Fix: index by a `ℕ`-sized type (`Fin D`) in the statement.
  (b) `Set.mem_sdiff` takes the element as an *explicit* argument
      (`Set.mem_sdiff e`), so `Set.mem_sdiff.mp` does not exist.
  (c) `rw [← h]` rewrites every occurrence of the RHS of `h`, including those
      inside other terms (e.g. inside `Real.sqrt γ`); use `conv_lhs` or
      `nlinarith` instead.
  (d) `Covers M X` is a `def`, so `rw` cannot see `matchVert M` inside it: add
      `Covers` to the `rw` list (or use `show`).
  (e) `set X := <big expr> with hX` followed by `simp only [..., hX]` can
      time out; prefer explicit `have` statements about the pieces.
  ADDED LATER IN THE SAME SESSION:
  * `S12Step8.lean` gained `chromaticIndex_le_of_matchingDecomposition`
    (a family of `n` pairwise edge-disjoint matchings covering `𝓗` gives
    `χ'(𝓗) ≤ n`, the final packaging of Step 10) and
    `IsS12Colours.card_Cprev`/`card_Cprev_real` (`(eqn:bound_prev_colours)`:
    `C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff` and `C_final` partition `[n]`,
    so `|C_prev| = n - |C_final|`).
  * NEW MODULE `Submission/EFL/S12Step9.lean` (in the cone): the counting part
    of §12 Step 9.  **`s12_mbound`** proves the three bounds
    `(eqn:mbound_1)`--`(eqn:mbound_3)` for
    `m(w) = |{c : w ∉ V(M_c)}|` from the covering properties of `𝓜_prev^*`
    (split as `𝓜_diff` with `ιdiff.ncard ≤ 1` and the rest): `𝓜_diff` covers
    `V^{(n-1)}` and `V^{(n-2)} ∩ S₁`, the rest has defects in `S₁` and misses
    each `u ∈ U` at most once, and covers `U` perfectly when
    `|U| ≤ (1-10ε)n`.  Note the subtle point (important!) that the second half
    of `(eqn:mbound_2)` (`m(v) ≤ 1` for `v ∈ V^{(n-2)}`) is proved by splitting
    on `v ∈ S₁`: if `v ∈ S₁` then the `𝓜_diff`-matchings cover `v`
    (`(def:r1s1)`) and at most one of the rest misses it; if `v ∉ S₁` then *no*
    matching of the rest misses it (its defects lie in `S₂ ⊆ S₁`) and at most
    one `𝓜_diff`-matching does.
  * **`s12_uc3_count`** proves the second half of UC3 (there are at least
    `|C_final|` vertices of degree `< |C_final|` in `𝓗_final`): the vertices of
    `V^{(n-1)}` missed by no matching, the vertices of `U ∖ V^{(n-1)}` (UC2)
    and the vertices outside `U` (UC1) form three disjoint sets of vertices of
    degree `< |C_final|`, and their union has at least
    `(|V^{(n-1)}| - |ι|) + (|U| - |V^{(n-1)}|) + (n - |U|) = n - |ι| =
    |C_final|` elements, because each matching misses at most one vertex of
    `U`.
  * **`s12_uc`** derives the degree bounds **UC2, UC3 (first half) and UC4**
    for `𝓗_final` from `(eqn:deg_h_final)` (`s12_deg_h_final`) and the
    `m(w)`-bounds, using the characterisations of `V^{(n-1)}`/`V^{(n-2)}` by
    the degrees and `d_𝓗(w) ≤ n-1`.
  * Also in `S12Step9.lean`: the singleton-edge facts
    `singles_regHypergraph_eq_zero_of_mem_Vplus` and
    `singleton_notMem_edgeSet_regHypergraph` (a vertex of `U` has no singleton
    edge in `𝓗_reg` because `d_𝓗(u) ≥ (1-ε)n > n - 3`; this is what makes the
    `hsingle` bookkeeping of `s12_deg_h_final` trivial on `U`), and the
    assembly glue `famOf_union`, `IsMatching.union` and
    `edgeDisjointFam_famOf_of_disjoint`, and
    `degAt_Rres_le_of_notMem_Vplus` (the reservoir estimate
    `d_{R_res}(w) ≤ ρ(1-ε)n + ξn` for `w ∉ U`, for each of the three reservoir
    types -- the Type B case uses that the `G'`-neighbourhood of `w ∉ U`
    consists of the `U`-neighbours of `w`, hence is contained in the
    `G`-neighbourhood), which is the input of UC1; **`s12_uc1`** then combines
    it with the decomposition `d_{𝓗_final}(w) ≤ d_{R_final}(w) + 2n/r₀`
    (`R_final ⊆ R_res`, the large edges account for the second term) and the
    two numerical inequalities of the paper to give `d_{𝓗_final}(w) ≤
    |C_final| - ρεn/4` for `w ∉ U`.
  * NEW MODULE `Submission/EFL/S12Numeric.lean` (in the cone): the numerical
    plumbing of the assembly -- `Dparam_ge_sub`, `n_le_two_Dparam`
    (`n ≤ 2D` for `ρ ≤ 1/4`, `n ≥ 8`), `two_thirds_beta_le`
    (`2βD ≥ (2/3)βn + 2` from `βn ≥ 6` and `n ≤ 2D`), `EP2num_le`
    (`r₁n/(r₀-1) ≤ 2βD`), `overlap_le_gamma_mul` (`r₁n/(r₀-1) ≤ γD`),
    `D'param_ge_half` (`10γ^{1/2}D/2 ≤ D'` when `10γ^{1/2}D ≥ 2`) and
    `four_gamma_le_sqrt` (`4γ ≤ 100γ^{1/2}` for `γ ≤ 625`), together with the
    bridges `hdeg_eq_hypergraphDegree` (`MultiHypergraph.hdeg = hypergraphDegree`)
    and `hdeg_largeEdges_le` (`d_{𝓗_large}(w) ≤ 2n/r₀`) with
    `hdeg_sub_le_degAt_add` (`d_{𝓗_final}(w) ≤ d_{R_final}(w) + d_{𝓗_large}(w)`
    when `𝓗_final ∖ R_final` consists of large edges), i.e. the decomposition
    `hdecomp` used by `s12_uc1`.
  NEXT: (i) §12 Step 8 rest (`stat:r_rem`: `Δ(G_final) - δ(G_final) ≤ 22εn` and
  lower `(ρ/4, ε^{1/3})`-regularity of `G_final` in the Type A₂ case) and UC1
  (which needs the reservoir degree bound for `w ∉ U`) and the second half of
  UC3 (the count of vertices of degree `< |C_final|`); (ii) **the assembly of
  `𝓜_prev`** from the outputs of Steps 4--7 (indexed by
  `C_prev = C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff`), supplying the
  hypotheses of `s12_mbound`/`s12_uc` and the `hsingle` condition of
  `s12_deg_h_final` (the singleton-edge bookkeeping of `𝓗_reg`: a vertex of
  `U` has no singleton at all since `d_𝓗(v) ≥ (1-ε)n > n-3`, so the
  bookkeeping only concerns the vertices outside `U`); (iii) Step 10 and the
  assembly (`𝓜_final` via Vizing / `optcol_corollary` /
  `hall_based_finishing`, then `𝓜_prev ∪ 𝓜_final` gives
  `𝓗.chromaticIndex ≤ n` through `chromaticIndex_le_of_matchingDecomposition`);
  (iv) the `eflStatementThreshold` wrapper and `theorem_1_1`.

* SESSION NOTE (current stretch, part 9) -- **§12 STEP 8 (`stat:r_rem`) IS
  COMPLETE**: the Type A₂ equilibrium analysis of `G_final`.  New cone module
  `Submission/EFL/S12Step8r.lean`:
  * **`(eqn:deficit)`** = `s12_deficit`: if `R_final = R_res ∖ ⋃_i S i`, the
    families `S i` for `i ∈ t` are matchings and the remaining ones contribute
    at most `C` edges through any vertex (after intersecting with `R_res`),
    then `d_{R_res ∖ R_final}(w) ≤ |t| + C`.  The proof uses
    `iUnion_eq_biUnion_finset`, `nbrs_union`, `Commons.Combinatorics.Set.
    ncard_biUnion_le` and `degAt_mono`.  In the application `t` indexes
    `𝓜_diff ∪ 𝓜_hm ∪ 𝓜_buff` (so `|t| ≤ 1 + 3γn/2 + D' ≤ 15γ^{1/2}n` after
    the numerics) and `C = 2γD` comes from MA2(i).
  * **`stat:r_rem`, first half** = `s12_delta_le`: from
    `(ρ - 20ε)n ≤ d_{R_res}(w) ≤ (ρ + ξ)n` (the Type A₂ reservoir bounds),
    `(eqn:deficit)` and the splitting
    `degAt R_res v ≤ degAt R_final v + degAt (R_res ∖ R_final) v` one gets
    `Δ(G_final) - d_{G_final}(v) ≤ 22ε n` for every `v` -- exactly the
    hypothesis of `optcol_corollary` (`OptCol.lean`/`OptColOdd.lean`).  The
    helper `hypergraphMaxDegree_le_of_le` converts a real upper bound on all
    degrees into `Δ ≤ M`.
  * **`stat:r_rem`, second half**: the counting lemmas
    `edgeCount_induce` (`e_G(A,B)` is unchanged when `G` is restricted to the
    edges inside `U`, for `A,B ⊆ U`), `fibreCount_ge_real`
    (`|N_R(b) ∩ A| ≥ |A| - (n - d_R(b))`) and `edgeCount_ge_of_deg`
    (`e_R(A,B) ≥ (|A| - εn)|B|` when every `b ∈ B` has degree ≥ `(1-ε)n`),
    applied to `G' = incidentTwo 𝓗 U` (`edgeCount_incidentTwo_ge`) give
    `e_{G'}(A,B) ≥ (|A| - εn)|B|` for `A,B ⊆ U`.  Combining with the Type A₂
    fields (`R_abs` lower `(ρ/2,ξ)`-regular; `R_abs ⊆ R_res`), the robustness
    Proposition 10.3.1 (`lowerRegular_of_delete`, with the deletion parameter
    `α` and `√α` the increase of `ξ`) and the monotonicity
    `SelfLowerRegular.mono`, `s12_selfLowerRegular_U` proves that the induced
    family `G_final[U] = induceU R_final U` is lower `(ρ/3, η)`-regular on
    `U`; then `s12_lowerRegular_final` applies Proposition 10.3.2
    (`selfLowerRegular_mono`, with `|V(𝓗) ∖ U| ≤ 10εn`) to conclude
    `SelfLowerRegular R_final Set.univ (ρ/4) (ε^{1/3})` -- again exactly the
    hypothesis of `optcol_corollary`.
  LEAN LESSONS (new, important):
  (a) `rw [h]` with `h : ε = √ε * √ε` rewrites *every* occurrence of `ε`,
      including the one inside `√ε`, producing `√(√ε*√ε)`.  Always orient the
      equation so the pattern is the composite side
      (`hs' : √ε * √ε = ε` then `rw [hs']`), or use `conv`.
  (b) `linarith`/`nlinarith` cannot substitute a nonlinear equality for an
      atom; do the rewrite by hand and chain the inequalities with `calc`.
  (c) `nlinarith` needs the nonnegativity of products as explicit hypotheses
      (e.g. `0 ≤ |A| * |B|`) when multiplying an inequality through.
  (d) `Finset` has no `Compl` instance without `[DecidableEq ι]`; either add
      it (harmless) or use `Finset.mem_compl.mpr`.
  (e) `Finset.sum_const` + `nsmul_eq_mul` + `mul_one` leaves the coercion goal
      `↑card = card`, closed by `norm_num`.
  (f) `Set.mem_sdiff` takes the element as an *explicit* argument;
      `Set.mem_sdiff.mp` does not exist.
  (g) to unfold `degAt` in a goal, use `show (nbrs _ _).ncard ≤ _` (`rw [degAt]`
      can fail "failed to rewrite using equation theorems for degAt").
  (h) `hypergraphMaxDegree_eq_sup`/`degAt_le_maxDegree` live in `OptCol.lean`.
  NEXT (the only remaining pieces of §12): the assembly of `𝓜_prev` (supplying
  the hypotheses of `s12_deficit`/`s12_delta_le`/`s12_selfLowerRegular_U`/
  `s12_lowerRegular_final` and of Step 9), §12 Step 10 (`𝓜_final` via Vizing /
  `optcol_corollary` / `hall_based_finishing` and the final packaging through
  `chromaticIndex_le_of_matchingDecomposition`), and the `eflStatementThreshold`
  wrapper -- plus the deep inputs themselves.

* SESSION NOTE (current stretch, part 10) -- **THE `𝓜_prev` ASSEMBLY IS
  UNDERWAY** (part 1: the structural glue, in the cone).  New module
  `Submission/EFL/S12Mprev.lean`:
  * `prevFam MD HM MM MB Cdiff Cmain Cbuff c` -- the family `𝓜_prev^*` of
    vertex sets of §12: the colour `c` carries the matching of the step whose
    colour set contains `c` (`famOf (MD c)` for `c ∈ C_diff`, `famOf (MM c)`
    for `c ∈ C_main`, `famOf (MB c)` for `c ∈ C_buff`, and `famOf (HM c)`
    otherwise, i.e. for `c ∈ C_med ∪ C_huge`); the five colour sets are
    pairwise disjoint, so only one branch is nonempty on `C_prev`.  Branch
    lemmas: `prevFam_of_mem_Cdiff`/`_Cmain`/`_Cbuff`/`_of_notMem`,
    `prevFam_eq_empty` (supported on `C_prev`), `prevFam_subset_union`,
    `famVert_prevFam`.
  * `isMatching_prevFam` (each member is a matching of `𝓗_reg`, from
    `isMatching_famOf_reg`) and `isMatching_prevFam_toFam` (deleting the
    singletons gives a matching of `𝓗`), plus the general glue
    `edgeDisjointFam_of_disjoint`, `famOf_union_four` and
    `sdiff_famVert_prevFam_subset` (coverage transfers from the branch
    containing the colour).
  * **`matchVert_toFam_of_mem_famVert`**: for `u ∈ U` and a sub-multi-hypergraph
    `𝓜 ≤ 𝓗_reg`, "covered" means the same in `𝓜` and in `𝓗` -- because
    `𝓗_reg` has no singleton edge at a vertex of `U`
    (`singles_regHypergraph_eq_zero_of_mem_Vplus`).  This is the bridge that
    lets the coverage statements of Steps 5--7 (phrased with `famVert`) be used
    for `matchVert`.
  * the defect sets of Steps 4--7, `S1def Vn2 S Mdiff C`,
    `S2def U S₁ Mhm (Cmed ∪ Chuge)`, `S3def U S₂ Mmain Cmain`, with
    `S1def_subset`, `S2def_subset`, `S3def_subset`,
    `mem_matchVert_of_mem_S2def`/`...S3def` (a vertex of `S₂`/`S₃` is covered
    by *every* matching of `𝓜_hm`/`𝓜_main`), `vn2_inter_S1_subset_matchVert`
    (`(def:r1s1)`: `V^{(n-2)} ∩ S₁` is covered by every `𝓜_diff`-matching) and
    `sdiff_famVert_prevFam_subset_S1` (the `hrestcov` hypothesis of
    `s12_mbound`: for `c ∉ C_diff`, `U ∖ V(𝓜_prev(c)) ⊆ S₁`).
  * **`ncard_miss_le_one`** (the `hnp` hypothesis of `s12_mbound`): at most one
    matching of `𝓜_hm ∪ 𝓜_main ∪ 𝓜_buff` misses a given `u ∈ U`.  The proof
    uses the definitions of `S₂`/`S₃`: a vertex of `S₂` is covered by all of
    `𝓜_hm` and a vertex of `S₃` by all of `𝓜_main`, so a miss by one family
    forces the others to cover.
  * `prevFam_subset_hyp` (every element of `𝓜_prev^*` is an edge of `𝓗`),
    `ncard_single_miss_eq_zero` and **`prevFam_single_bound`**: the `hsingle`
    bookkeeping of `s12_deg_h_final` is *vacuous* for `𝓜_prev`, since all four
    steps produce matchings of `𝓗` (not of `𝓗_reg`) -- the singletons only
    appear in the *nibble* object `N_c`, which is replaced by `toFam N_c`
    before it enters `𝓜_prev`.
  * `hfinOf`/`mem_hfinOf` (`𝓗_final = 𝓗 ∖ ⋃𝓜_prev` with the index type
    `↥C_prev`) and `card_Cprev_sub` (`|C_prev| = n - |C_final|`, the `hcard`
    hypothesis of `s12_deg_h_final`, from `IsS12Colours.card_Cprev_real`).
  LEAN LESSONS: (i) `if c ∈ S then ... else ...` (without the `h :` binder) is
  `ite`, so the lemmas are `if_pos`/`if_neg`, not `dif_pos`/`dif_neg`;
  (ii) `Finset.eq_empty_iff_forall_notMem` (capital `M`) is the Finset version
  of the empty-set criterion; (iii) a statement mentioning `Finset.filter` with
  a propositional predicate needs `open Classical` at the top of the section
  (otherwise `DecidablePred` cannot be synthesised outside a tactic block).
  PART 2 of the same module (added later in the same session): the **ambient
  vertex-set data of the instantiation**.  `hdeg_le_pred` (`d_𝓗(v) ≤ n-1`, from
  `degree_mul_le`), `two_mul_hdeg_sub_le_degAt` (the paper's
  `eqn:non-graph-degree`, `2 d_𝓗(v) ≤ (n-1) + d_G(v)`, from
  `hdeg_sdiff_pow2_le` and the decomposition `hdeg 𝓗 = hdeg (𝓗∖𝓗²) + degAt`),
  the inclusions `Vdeg_pred_subset_Vplus` (`V^{(n-1)}(𝓗) ⊆ U`, needing
  `εn ≥ 1`), `Vdeg_pred2_subset_Vplus` (`V^{(n-2)}(𝓗) ⊆ U`, needing `εn ≥ 3`)
  and `Vdeg_plus_subset_Vplus` (`V_+^{(n-2)}(𝓗) ⊆ U`, the hypothesis `hVn2U` of
  `s12_mbound`), the characterisations `mem_Vdeg_pred_iff`/`mem_Vdeg_plus_iff`
  (the hypotheses `hVn1`/`hVn2` of `s12_uc`), and the abbreviations
  `Vn1set = Vdeg 𝓗 (n-1)`, `Vn2set = Vdeg 𝓗 (n-1) ∪ Vdeg 𝓗 (n-2)` with
  `Vn1set_subset_Vn2set` (`hVn1Vn2`).  NOTE: `Vdeg 𝓗 d` is the *exact*
  hypergraph degree `{v : d_𝓗(v) = d}`, so `V_+^{(n-2)}` is the union of the
  `n-1` and `n-2` parts (not `Vdeg 𝓗 (n-2)` alone).
  PART 3 of the same module (added later in the same session): the
  **instantiation entry points**, i.e. the §12 Steps 1--3 link.
  `s12_step3_typeA` applies `exists_S12Colours_typeA` and returns, together
  with the seven colour sets and `IsS12Colours`, the facts
  `φ.SingletonClassesForHuge β` (consumed by Steps 4/5/6), `Vn2set 𝓗 ⊆ U` and
  the two characterisations `v ∈ Vn1set 𝓗 ↔ (n-1 : ℝ) ≤ d_𝓗(v)`,
  `v ∈ Vn2set 𝓗 ↔ (n-2 : ℝ) ≤ d_𝓗(v)` (the `hVn1`/`hVn2` of `s12_uc`);
  `s12_step3_typeB` is the Type B analogue: `U = V_+^{(1-ε)}(G)` and the
  extremal huge-class bound `∀ c, φ.AssignedToHuge β c → |V(φ⁻¹(c))| ≤ δn`
  (which is what Step 5's `hbigsize` needs in the Type B case).  Both take the
  numerical part of the hierarchy as explicit hypotheses.
  PART 4 of the same module (added later in the same session): **§12 Step 2**
  and the **Step-4 instantiation**.
  * `cvFinset φ U` -- the family `𝓥` of `(def:cv)`, i.e. `{U, V(𝓗)}` together
    with `U ∪ V(φ⁻¹(c))` and `U ∖ V(φ⁻¹(c))` for every colour `c`, with
    `mem_cvFinset` (and the four membership lemmas `mem_cvFinset_U`,
    `mem_cvFinset_univ`, `mem_cvFinset_union`, `mem_cvFinset_sdiff`) and the
    size bound `cvFinset_card_le` (`|𝓥| ≤ 2n+2`, the hypothesis `|𝓥| ≤ n^{log n}`
    of Property 11.1).  NOTE: the paper's `𝓥` uses `V(φ⁻¹(c))`; the cone uses
    `φ.classVertices c` (equal to `matchVert (colourFam φ c)`), and the
    absorbers are stated for the coerced `Set` version.
  * `IsS12Step4` -- the output package of Step 4 (D1, `(eq:R1abs)`,
    `(eq:boundS1)`) as a named `Prop` (so that later steps can consume it
    without restating eleven conjuncts).
  * **`s12_step4_inst`** -- the Step-4 instantiation: given the Step-3 colour
    sets, the Type A hypothesis, the margins `DiffMargins n β`, the absorber
    `R_abs` of §11 (for `10ξ`, i.e. the `(ρ_abs, 10ξ, ξ)`-absorber that Step 2
    provides) and `10ξ + 1/n ≤ 3γ/2`, either `χ'(𝓗) ≤ n` or `IsS12Step4` holds.
    (The unused `ε` parameter of `s12_step4` is supplied from the `U = V_+^{(1-ε)}(G)`
    convention.)
  NEXT: (a) the rest of the *instantiation*: run `s12_step5` (`HugeMargins`, `InternalMatchingInput`,
  the `𝓥`-memberships of `U ∪ V(φ⁻¹(c))`/`U ∖ V(φ⁻¹(c))` from `(def:cv)`),
  `s12_step6` (`DegreeMargins`, the nibble) and `s12_step7` (the leftover),
  defining `R₂ = R₁ ∖ ⋃𝓜_hm` and `R₃`, and discharging `hrestcov`, `hnp` and the
  `d_𝓗`-counts with the lemmas of parts 1--3; (b) `s12_uc1`'s hypotheses (`d_{R_res ∖ R_final} ≤ 15γ^{1/2}n`
  from `s12_deficit`, the large-edge count `hdeg_largeEdges_le`); (c) the
  pairwise edge-disjointness of `𝓜_prev` (from the colour-class disjointness and
  the `R`-deletions `R₂ = R₁ ∖ ⋃𝓜_hm`, `R₃ = R₂ ∖ ⋃𝓜_main`); (d) Step 10 and
  the final packaging.


* SESSION NOTE (current stretch, part 11) -- **§12 STEP 10 IS COMPLETE**, and
  **§12 STEP 5 IS PACKAGED**.  Two new cone modules.

  `Submission/EFL/S12Step10.lean` (the last step of §12):
  * `S12Finishing 𝓗 φ Cfin Rfin Mfin` -- the output package of Step 10: `Mfin`
    is supported on `C_fin` (`support`), extends the colour classes of `φ` on
    `C_fin` (`extends_class`), every `Mfin c` is a matching (`matching`) and
    the `Rfin`-edges are covered (`covers`).
  * `exists_finishing_of_colorable` (Cases A1 and A2 together): a colouring of
    the leftover 2-graph `R` with `|C_fin|` colours plus the vanishing of
    `φ⁻¹(c)` on `C_fin` (the paper's (T1)) gives `S12Finishing`, by
    `subFam`-ing the colour classes of `R` and re-indexing along
    `Cfin.orderIsoOfFin`.  `exists_finishing_vizing` is the Vizing-shaped
    corollary taking a pair-family colouring
    (`Commons.Combinatorics.SimpleGraph.edgeColoring_of_pairFamily`).
  * Case B: `finalColoursAt φ Cfin w` is the paper's
    `C_w = {c ∈ C_fin : w ∈ V(φ⁻¹(c))}`; `exists_finishing_hall` shows that a
    Hall-finishing valuation `ψ : R → C_fin` avoiding `C_w` at both ends of
    every edge makes `ψ⁻¹(c) ∪ φ⁻¹(c)` a matching (the cross-term uses
    `ψ(e) ∉ C_w` at a shared vertex), and
    `exists_finishing_hall_of_margins` discharges the hypotheses of Lemma 10.2
    from the paper's numerical data using the newly proved commons lemma
    `Commons.Combinatorics.SimpleGraph.hallFinishing_of_pairFamily`.
  * the final packaging: `chromaticIndex_le_of_decomposition` (a family
    `Mprev` supported on `C_prev` together with a family supported on the
    disjoint `C_fin`, covering all edges, gives `χ'(𝓗) ≤ n`) and
    `chromaticIndex_le_of_prev_and_finishing` (the same with the covering
    hypothesis in the paper's form: every edge is in `𝓜_prev`, in `R_final`
    or in a colour class of `C_fin` -- which is exactly what
    `s12_h_final_decomposition` of `S12Step8.lean` provides).
  * `nbrs_eq_pair_offdiag`/`degAt_eq_pair_offdiag` restate `degAt` in the
    off-diagonal pair form expected by the pair-family commons lemmas.

  `Submission/EFL/S12Inst5.lean`:
  * `IsS12Step4` in `S12Mprev.lean` was converted from a `def` with eleven
    `∧`-conjuncts into a `structure` with named fields (`hMdiff_supp`,
    `hMdiff_ext`, `hMdiff_add`, `hMdiff_mat`, `hMdiff_cov`, `hMdiff_five`,
    `hR₁_eq`, `hS₁_eq`, `hS₁_sub`, `hR₁_abs`, `hS₁_big`); this makes the
    assembly much easier to read.  `s12_step4_inst` was updated accordingly.
  * `card_chuge_union_cmed_le` -- `(eqn:size_hm)`, `|C_huge ∪ C_med| ≤ 3γn/2`
    (from `natCard_hugeEdges_le` and `hCmed_size`).
  * `s12_step5_inst` -- `s12_step5` with every hypothesis discharged: the
    `𝓥` of `(def:cv)` (`mem_cvFinset_U/univ/union/sdiff`), `B = 0` with
    `internalMatchingInput`, `hUdeg` from `U = V_+^{(1-ε)}(G)`, `hbigsize`
    from `IsS12Colours.huge_class_inter_U_le` + `SingletonClassesForHuge`,
    `hmedsize` from `hCmed_vertex`, `hnotdiff` from `hCdiff_full`, `hNR₁`
    (colour classes have edge size `> r₁ ≥ 2`, so they miss `R₁ ⊆ 𝓗²`), `hk`
    as above.
  * `hdeg_famUnionFinset_le_card` -- the union of a family of matchings has
    degree at most the number of colours at every vertex (via
    `Commons.Combinatorics.Set.ncard_biUnion_le` plus
    `MultiHypergraph.hdeg_famOf_le_one`).
  * `IsS12Step5` -- the output package of Step 5 (HM1, HM2, `(eq:R2abs)`,
    `(eq:boundS2)`), and `s12_step5_pack`, which produces it from
    `IsS12Step4`: `R₂ = R₁ ∖ ⋃𝓜_hm` is a `(ρ_abs, 2γ, ξ)`-absorber by
    `IsAbsorber.delete` applied to the *sharper* `(10ξ)` absorbability of
    `R₁` (the paper's `ξ ≪ γ`: `10ξ + 3γ/2 ≤ 2γ`) with
    `Δ(R₁ ∖ R₂) ≤ |C_huge ∪ C_med| ≤ 3γn/2`, and `S₂ = S₁ ∖ ⋃_c (U ∖ V(M_c))`
    loses at most `|C_huge ∪ C_med|` vertices, giving `(eq:boundS2)` from the
    Step-4 bound `|S₁| ≥ |S| - 5` and `(eqn:rs)`.
  LEAN LESSONS: (i) `IsAbsorber.mono_gamma` *increases* γ (weaker), so to get
  a *smaller* γ for the same absorber one must re-run the argument with the
  sharper input, not weaken at the end; (ii) `rw [h]` inside a goal whose RHS
  also contains the rewritten term rewrites BOTH occurrences -- use
  `conv_lhs => rw [h]`; (iii) `set x := e with h` then `rw [h]` can leave
  goals that are `rfl` (the local abbreviation unfolds), so a following
  `exact` may report "no goals to be solved"; (iv) an implicit argument that
  does not occur in the conclusion (here `S` of `s12_step5_inst`) must be
  passed explicitly as `(S := S)`; (v) `lake env lean F.lean` does NOT
  refresh the olean of `F`, so after editing `S12Mprev.lean` a
  `lake build Submission.EFL.S12Mprev` is required before an importing file
  sees the new version (a `def`->`structure` change otherwise silently keeps
  the old projection-free type).

  NEXT: (a) the Step-6 and Step-7 wrappers (`S12Step6Result` /
  `S12Step7Result` are already stated as `Prop`s in `S12Step6.lean` /
  `S12Step7.lean`; they take most of their hypotheses directly, so the work is
  bookkeeping, with `R₃ = R₂ ∖ ⋃N_c` and `S₃ = S₂ ∖ ⋃_c(U ∖ V(N_c))`);
  (b) Step 9: apply `s12_mbound` and `s12_uc` to `𝓜_prev^*` (the
  `famVert_prevFam` family of `S12Mprev.lean`), discharging `hdiff1`,
  `hdiffVn1`, `hdiffVn2`, `hrestcov`, `hnp`, `hperf` from the Step-4/5/6/7
  data via `vn2_inter_S1_subset_matchVert`, `sdiff_famVert_prevFam_subset_S1`,
  `ncard_miss_le_one`;
  (c) Steps 8 and 10 wiring: UC1 (`s12_uc1` with `s12_deficit`), the count
  `s12_uc3_count`, and `chromaticIndex_le_of_prev_and_finishing`;
  (d) Step 1: the constant hierarchy and `largeEdgeThmStatement_of_deep`;
  (e) the deep input `Prop`s (`NibbleStatement`, `LeftoverStatement`, Kahn,
  Molloy-Reed, AKS, GKO, EGJ, `lem:embed`).


* SESSION NOTE (current stretch, part 12) -- **§12 STEP 9 IS PACKAGED**.
  New cone module `Submission/EFL/S12Step9Pack.lean`:
  * `prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff c` -- `𝓜_prev^*`
    (`prevFam` of `S12Mprev.lean`) extended by `Set.univ` outside
    `C_prev = C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff`, so that it is a
    family indexed by ALL of `Fin n` whose matchings miss nothing off
    `C_prev` (`famVert_prevFamFull_of_notMem`).  This is what makes the counts
    of `s12_mbound` (an `ι`-indexed family of vertex-set families) comparable
    with the `Finset.filter` counts of `S12Mprev.lean`.
  * `prevMiss ... w` -- the set `{i | w ∉ famVert (𝓜_prev^*_i)}` of colours
    whose matching misses `w`; this is exactly the `m(w)`-index sets of
    `(eqn:deg_h_final)` and `s12_uc`.
  * branch lemmas `prevFamFull_of_mem`, `prevFamFull_of_notMem`,
    `famVert_prevFam_eq_Cdiff/_Cmain/_Cbuff/_HM` (the `famVert` of `prevFam`
    in each of the four branches), and the membership helpers
    `mem_prev_of_mem_Cmed/_Cdiff/_Chuge/_Cmain/_Cbuff`,
    `mem_of_mem_prev_notMem_Cdiff`, `mem_med_huge_of_mem_prev`.
  * **`s12_step9_mbound`** -- `s12_mbound` instantiated with
    `ι := Fin n`, `M := prevFamFull ...`, `ιdiff := C_diff`.  Every hypothesis
    is discharged: `hdiff1` from `Cdiff.card ≤ 1`; `hdiffVn1`/`hdiffVn2` from
    the Step-4 coverage of `V^{(n-1)}(𝓗)` and `(def:r1s1)`; `hrestcov` from
    `sdiff_famVert_prevFam_subset` (with `U \ V(M_c) ⊆ S₂ ⊆ S₁` for the
    `C_main` branch and `⊆ S₃ ⊆ S₂ ⊆ S₁` for the `C_buff` branch); `hnp` from
    `ncard_miss_le_one` (the sum of the three `Finset.filter` counts is `≤ 1`,
    so the off-`C_diff` miss set is too, via
    `Commons.Combinatorics.Set.ncard_biUnion_le`-free elementary union
    bounds); `hperf` from the three perfect-coverage statements.
  LEAN LESSONS: (i) `{i | P i} ⊆ ↑F` is NOT `∀ i, P i → i ∈ F` -- `hi` has to
  be re-read as the proposition (`rw [...] at hi` fails on a set-builder
  membership, since `hi`'s type is `i ∈ {i | ...}`); use `rintro` patterns to
  destructure the set-builder membership directly; (ii) `Finset.mem_union_left`
  takes the SECOND set as its explicit argument, so for
  `A ∪ (B ∪ C)` the three cases are `Finset.mem_union_left (B ∪ C)`,
  `Finset.mem_union_right A (Finset.mem_union_left C)`,
  `Finset.mem_union_right A (Finset.mem_union_right B)`; (iii) the association
  of `A ∪ B ∪ C` (left-nested) must match the `Finset.card_union_le` splits
  exactly, otherwise `omega` sees unrelated atoms; (iv) `u ∉ (Set.univ : Set _)`
  is a FUNCTION `u ∈ Set.univ → False`, so `hi trivial` gives `False` and one
  needs `(hi trivial).elim`; (v) `Set.ncard_coe_finset` (lowercase) is the
  `@[simp, norm_cast]` lemma `(s : Set α).ncard = s.card`.
  NEXT: `s12_uc` can now be instantiated in exactly the same way (`hVn1`/`hVn2`
  from `mem_Vdeg_pred_iff`/`mem_Vdeg_plus_iff`, `hdg_le` from `hdeg_le_pred`,
  and `hm2`/`hm2'`/`hm0` from `s12_step9_mbound`); the remaining work is the
  assembly (Steps 4--7 wiring, UC1 via `s12_uc1`/`s12_deficit`/`s12_delta_le`,
  Step 10 via `chromaticIndex_le_of_prev_and_finishing`, and Step 1's constant
  hierarchy).


* SESSION NOTE (current stretch, part 13) -- **CASE A₁ OF §12 STEP 10 IS NOW
  FULLY INSTANTIATED**; two more commons lemmas landed.
  * FLEET: `Commons.Combinatorics.SimpleGraph.hallFinishing_of_pairFamily`
    (Lemma 10.2 in pair-family form) and
    `Commons.Combinatorics.SimpleGraph.edgeColoring_of_pairFamily` (Vizing in
    pair-family form: a family of two-element subsets with maximum vertex
    degree `D` has a proper `(D+1)`-edge-colouring).  The latter was ported
    into the cone by appending it to
    `Submission/EFL/Comm/EdgeColoringPairFamily.lean` (the file is safe: its
    imports are `Mathlib.Data.Set.Card` and the two commons vizing modules).
    NOTE: the commons FILE for `edgeColoring_of_pairFamily` starts with
    `import Mathlib`, so it must NOT be imported directly into the cone -- use
    the ported copy in `Submission/EFL/Comm/EdgeColoringPairFamily.lean`
    (`DiffAbs2.lean` already imports it, hence it is in the cone).
  * `Submission/EFL/S12Step10.lean` gained
    `exists_finishing_vizing_of_degAt`: from `R ⊆ 𝓗`, `edgeSize e = 2` on `R`,
    `degAt R w ≤ |C_fin| - 1` and the vanishing of `φ⁻¹(c)` on `C_fin`, it
    produces `S12Finishing` via the ported Vizing lemma (with
    `Fin.cast (Cfin.card - 1 + 1 = Cfin.card)`).  This is the paper's Case 1
    verbatim.  Case 2 (Type A₂) needs no new lemma: it is
    `exists_finishing_of_colorable` applied to `R.Colorable |C_fin|`, which the
    assembly gets from `optcol_corollary_even` (in `OptCol.lean`) with
    `Colorable.mono`.
  * LEAN LESSON: `exists_finishing_vizing`'s implicit colour count `D` is NOT
    inferable from the `Fin` type alone (it is determined by `hk : D ≤
    Cfin.card`), so `refine exists_finishing_vizing hRsub ?_ hempty (by omega)`
    silently instantiates `D := 1`; pass `(D := Cfin.card)` explicitly.


* SESSION NOTE (current stretch, part 14) -- **THE §12 ASSEMBLY IS UNDER WAY**.
  Two new cone modules.

  `Submission/EFL/S12Assem.lean` (in the cone, sorry-free, ~900 lines):
  * `isTypeA_exists_of_nonExtremal` / `isTypeB_exists_of_extremal`: the passage
    from Theorem 6.7's alternatives (`LargeEdgeNonExtremal`/`LargeEdgeExtremal`,
    colourings of *all* of `𝓗`) to the §12 hypotheses `IsTypeA`/`IsTypeB`
    (colourings of `𝓗_med ∪ 𝓗_large`), by restricting along
    `medLarge_subset`.  Supporting restriction lemmas:
    `Hypergraph.Coloring.restrict_labels`, `UsesColourSet_restrict`,
    `classVertices_restrict_subset`, `classVertexCount_restrict_le`,
    `AssignedToHuge_restrict`, `AssignedToHuge_of_restrict`,
    `SingletonClassesForHuge_restrict`, `colorClass_restrict_eq`.
  * `S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ`: the numerical hypotheses of the
    assembly (the paper's `1/n ≪ ξ ≪ 1/r₁ ≪ β ≪ κ ≪ γ ≪ ε ≪ ρ ≪ 1` in
    explicit form, including `HugeMargins`, `DegreeMargins` and the
    `D`-dependent inequalities).
  * `s12_step5_pack_gen`: §12 Step 5 packaged with the huge/medium size bounds
    (`|V(φ⁻¹(c)) ∩ U| ≤ εn` for c ∈ C_huge and `|V(φ⁻¹(c))| ≤ (3γ/2)n` for
    c ∈ C_med) supplied directly, so that it applies in Types A and B alike.
  * `s12_steps67`: §12 Steps 6 and 7 (the nibble and the leftover lemma) from
    the Step-4/5 data, returning `S12Step6Result` and `S12Step7Result`.
  * `S12Out`: the output of Steps 8/9 -- `𝓜_prev`, `R_final`,
    `𝓗_final = 𝓗 ∖ ⋃𝓜_prev`, `(eqn:h_final)`, `(eqn:deficit)`, the exact
    degree identity `d_{𝓗_final}(w) = d_{G_final}(w) + |C_w|` and the bounds
    `UC1`--`UC4` together with the count of `|C_final|` vertices of degree
    `< |C_final|`.
  * `isS12Step4_of_Cdiff_empty`: Step 4 in the case `C_diff = ∅` (Type B).
  * `hdeg_famUnionFinset_colourFam`: `d_{⋃_{c∈C} φ⁻¹(c)}(w) = |C_w|`
    (via `Set.ncard_le_ncard_of_injOn` in both directions).
  * `prevFam_pairwise_disjoint`: **the four families of `𝓜_prev` are pairwise
    edge-disjoint** -- the `hdisj` hypothesis of `s12_deg_h_final`.  The proof
    is a case analysis on the four branches of `prevFam` (via
    `prevFam_or_added`), using the `R`-deletions `R₁ ∩ ⋃𝓜_diff = ∅`,
    `R₂ ⊆ R₁ ∖ ⋃𝓜_hm`, `R₃ ⊆ R₂ ∖ ⋃N`, `𝓗_rem ⊆ ∖(R_res ∪ ⋃𝓜_diff ∪ ⋃N)`,
    the disjointness of the matchings within each step, and the fact that
    *added* edges have size `≤ r₁` while colour classes have size `> r₁` (so
    "colour vs added" is settled by size alone).

  `Submission/EFL/S12Core.lean` (**not yet in the cone**, still contains one
  `sorry` at the very end of `s12_core`; import it into `Submission.lean` once
  it is complete).  It contains the generic core of the assembly:
  * `subset_toFam_famOf`, `prevFam_or_added` (the decomposition of `𝓜_prev` at
    a colour into "colour class" or one of the four families);
  * `s12_core`: from Steps 4/5 (plus the nibble and leftover inputs) it runs
    Steps 6 and 7, defines `𝓜_prev := prevFamE Mdiff Mhm Mmain Mbuff ...`,
    `R_final := R_res ∖ ⋃𝓜_prev`, `𝓗_final := hfinOf ...`, and proves the
    fields of `S12Out`; currently the fields `hsup`, `hext`, `hmat`, `hRfin`,
    `hRfin2`, `hRfin_sub` and `hdecomp` ((eqn:h_final), proved directly from
    the reservoir/leftover coverage rather than through
    `s12_h_final_decomposition`) are done; `hfin_eq`, `hdeg_fin`, `hdeficit`
    and `UC1`--`UC4`/`hcount` remain.

  MODIFICATIONS OF EARLIER FILES (both cone files, both rebuilt):
  * `S12Step6Result` gained three conjuncts: (i) every edge of `Mmain c`
    (c ∈ C_main) lies in `⋃ N`; (ii) distinct `Mmain c` are pairwise disjoint;
    (iii) the defining equation `Mmain (colourEnum Cmain i) = toFam (N i)`.
    These are what makes `𝓜_main` usable in the disjointness proof and in the
    decomposition of `𝓗`.
  * `S12Step7Result` gained the conjunct `∀ c ≠ c', Disjoint (famOf (Mbuff c))
    (famOf (Mbuff c'))` (the leftover lemma's `F1`), needed for the same
    reason.

  REMAINING WORK (in dependency order):
  1. `hfin_eq : 𝓗fin = R_final ∪ ⋃_{c ∈ C_final} φ⁻¹(c)`.  The `⊆` direction
     uses `hdecomp`; the `⊇` direction needs `R_final ⊆ 𝓗fin` and
     `colourFam φ c ⊆ 𝓗fin` for c ∈ C_final, the latter by the size argument
     (added edges have size ≤ r₁, colour classes > r₁).
  2. `hdeg_fin : d_{𝓗_final}(w) = d_{R_final}(w) + |C_w|` from `hfin_eq`,
     `hdeg_union`, `hdeg_eq_degAt` and `hdeg_famUnionFinset_colourFam`.
  3. `hdeficit` from `s12_deficit` with `t := C_diff ∪ C_huge ∪ C_med ∪ C_buff`
     and `C := 2γ|C_main|`; the key instance is
     `R_res ∩ ⋃_{c∈C_main} Mmain c ⊆ R_abs ∩ ⋃N` (using conjunct (i) of the
     Step-6 result and the fact that colour-class edges have size `> r₁ ≥ 2`)
     together with conjunct 16 of `S12Step6Result`.
  4. `hUC1` (`s12_uc1`), `hUC2`/`hUC3`/`hUC4` (`s12_uc` with `ι := ↥C_prev`,
     after transferring the `m(w)`-bounds from `s12_step9_mbound` -- stated for
     `Fin n` -- to `↥C_prev`) and `hcount` (`s12_uc3_count`).
  5. The three *finishers* (Step 10): from `S12Out` + `(T1)` (Type A), or
     `(T2)` + the regularity of `G_final` (Type A₂), or the Hall data
     (Type B), produce `S12Finishing` and conclude `χ'(𝓗) ≤ n` via
     `chromaticIndex_le_of_prev_and_finishing`.
  6. Step 1: choose the constants (the nested minima along the hierarchy
     `1/n₀ ≪ 1/r₀ ≪ ξ ≪ 1/r₁ ≪ β ≪ κ ≪ γ₁ ≪ ε₁ ≪ ρ₁ ≪ σ ≪ δ ≪ γ₂ ≪ ρ₂ ≪ ε₂ ≪ 1`),
     apply `largeEdgeThmStatement_of_deep`, and discharge the hypotheses of
     `s12_core` (including all of `S12Margins` and the finishers' data).


* SESSION NOTE (current stretch, part 15) -- **PERFORMANCE OF THE §12 ASSEMBLY**
  (a crucial lesson for anyone continuing `S12Core.lean`).
  `Submission/EFL/S12Core.lean` (the generic core of the assembly, still with a
  trailing `sorry` at the end of `s12_core`; NOT in the cone) originally took
  **30 minutes** to elaborate; it now takes **28 seconds**.  Two causes, both
  worth remembering:
  1. **`tauto` is catastrophic here.**  Two `tauto` calls (splitting the
     membership `c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff` into the four-way
     disjunction) consumed millions of heartbeats each: replacing them by an
     explicit `rcases (((h1 | h2) | h3) | h4) | h5` chain (with
     `Or.inl`/`Or.inr`/`Finset.mem_union.mpr` for the two memberships that are
     `Finset` unions) cut the elaboration from 30 min to 20 s.  DO NOT use
     `tauto` on these union disjunctions.
  2. **`rw` with a `set`-introduced abbreviation does not beta-reduce.**
     `set Mprev : Fin n → Set 𝓗 := prevFamE ... with hMprevdef` makes `Mprev c`
     defeq to `prevFamE ... c`, but `rw [hMprevdef]` rewrites it to
     `(fun i => prevFamE ... i) c` — a beta-redex, so a subsequent
     `rw [prevFam_of_mem_Cdiff h]` (which looks for the *reduced* form) fails.
     Use `change <reduced form>` (which beta-reduces) or `simp only [hSdef]`.
     Also: with `set S := fun i => prevFam ... i`, all hypotheses stated in
     terms of `S i` are *displayed* in reduced form, so `rw [h0]` with
     `h0 : S i = ∅` fails; state such facts in the reduced (`prevFam`) form.
  3. Useful technique for localising a slow tactic: re-elaborate the file with
     `set_option maxHeartbeats 200000` (cheap, fails fast): the steps that need
     millions of heartbeats show up as `timeout` errors with their line
     numbers.

  STATE OF `S12Core.lean` (`s12_core`, the generic core of §12):
  done and compiling: Steps 6/7 (via `s12_step6` and `s12_step7`), the
  definitions of `Mprev`, `R_final`, `𝓗_fin`, the location/disjointness facts,
  `prevFam_pairwise_disjoint`, the membership helpers
  (`hMprev_of_*`/`hprevFam_to_Mprev`/`hMprev_to_prevFam`), the fields `hsup`,
  `hext`, `hmat`, `hRfin`, `hRfin2`, `hRfin_sub` of `S12Out`, the decomposition
  `hdecomp`, `hfin_eq`, `hdeg_fin` and the deficit bound `hdeficit` (via
  `s12_deficit` with `t = Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff`, `S := prevFam ...`
  and `C := 2γ|C_main|`; the key inclusion is
  `R_res ∩ ⋃_{C_main} Mmain ⊆ R_abs ∩ ⋃N`, proved from conjunct (i) of
  `S12Step6Result` and the fact that colour-class edges have size `> r₁ ≥ 2`).
  REMAINING: the `m(w)`-bounds and `UC1`--`UC4`/`hcount` (Steps 9), and the
  final `⟨Mprev, R_final, 𝓗fin, ...⟩` tuple.


  **IMPORTANT SUBTLETY for the `m(w)`-bounds (Steps 8/9).**  The paper's
  `𝓜_prev^*` is `𝓜_diff ∪ 𝓜_hm ∪ 𝓜_main^* ∪ 𝓜_buff` where `𝓜_main^* = {M_c^*}`
  is the *nibble* output `N_c` — i.e. a family of vertex sets **including the
  singleton edges** — whereas `𝓜_main` (the part that colours edges) is its
  "singletons removed" version `toFam (N_c) = Mmain c`.  Consequently:
  * the defect set of Step 6 is `S₃ = S₂ ∖ ⋃_{c ∈ C_main}(U ∖ V(N_c))` with
    `V(N_c) = famVert (N c)` (the *multi-hypergraph* vertex set), NOT
    `matchVert (Mmain c)`; the two differ by the vertices covered only by a
    singleton edge of `N c`.  (Accordingly `S3def` in `S12Mprev.lean`, which is
    phrased with `matchVert (Mmain c)` because it only has `Mmain` available,
    is NOT the same set as the `S₃` produced by `s12_step7`; using `S3def`
    in `s12_step9_mbound` requires care.)
  * the `m(w)`-counts of `(eqn:deg_h_final)` count matchings missing `w` in the
    *multi-hypergraph* sense (`w ∉ famVert (N_c)`), and the vertices covered
    only by singletons are accounted for by the `max(0, n-3-d_𝓗(w))` term
    (the hypothesis `hsingle` of `s12_deg_h_final`).  One therefore wants the
    index family `Mstar i := if i ∈ C_main then N (enum⁻¹ i) else prevFam … i`
    (mixing families of vertex sets) for `s12_deg_h_final`/`s12_uc`/`s12_mbound`,
    with `Mmain` used only where an *edge* (a member of `𝓗`) is needed.
  * CAVEAT (the counting of singletons): the cone's `EdgeDisjointFam` only
    forbids the *proper* (`≥ 2`-element) parts of two matchings from meeting
    (`MultiHypergraph.edgeSet`/`EdgeDisjointFam` in `Nibble.lean` deliberately
    let two matchings share a singleton `{v}`, mirroring "the singleton edges
    are available in several copies").  The paper's bound `|{i : M_i covers w
    only by a singleton}| ≤ max(0, n-3-d_𝓗(w))` therefore needs justification:
    in the application the matchings of `𝓜_main^*` come from the nibble lemma
    applied with the *inputs* `φ⁻¹(c) ⊆ 𝓗` (no singletons), and the construction
    is `N_i = N_i' ∪ M_i` with `N_i' ⊆ 𝓗'`, so the number of singletons used is
    controlled by `𝓗'`; alternatively one can discharge the hypothesis
    `hsingle` of `s12_deg_h_final` directly from the structure of the nibble
    lemma's output (rather than from a general multi-hypergraph matching fact).
  * for edges `e ∈ 𝓗` one has `2 ≤ e.ncard` (the hypothesis `hbig`), hence
    `e ∈ Mmain c ↔ (e : Set (Fin n)) ∈ N c`, so the two formulations agree on
    the edges of `𝓗`; this is what makes `hfin : e ∈ 𝓗_fin ↔ e ∈ 𝓗 ∧ ∀ i, e ∉ M i`
    work for `Mstar`.
  Two file-scope helpers
  `ncard_subtype_le`/`ncard_subtype_eq` are already provided for transferring
  the `m(w)`-bounds from `Fin n` (`s12_step9_mbound`) to the index type
  `↥C_prev` used by `s12_deg_h_final`/`s12_uc`.


* SESSION NOTE (current stretch, part 16) -- **§12 STEP 10 IS COMPLETE**
  (the three finishers).  New cone module `Submission/EFL/S12Finish.lean`
  (sorry-free, in the cone):
  * `degAt_R_final_of_T1`: in a Type A colouring the colour classes of `C_final`
    are empty (T1), so `(finalColoursAt φ Cfinal w).card = 0` and the identity
    `d_{𝓗_final}(w) = d_{G_final}(w) + |C_w|` of `S12Out` becomes
    `d_{R_final}(w) = d_{𝓗_final}(w)`.
  * `s12_finish_A1` (Type A₁): `Δ(R_final) ≤ |C_final| - 1`, obtained by
    splitting on `w ∉ U` (UC1 + `1 ≤ ρεn/4`), `w ∈ U ∖ V^{(n-1)}` (UC2) and
    `w ∈ V^{(n-1)}` (UC4, with its hypothesis `∀ v ∈ V^{(n-1)}, v ∉ S₁`);
    then Vizing in the pair-family form
    (`exists_finishing_vizing_of_degAt`) and
    `chromaticIndex_le_of_prev_and_finishing`.
  * `s12_finish_A2` (Type A₂): the same Vizing step if `Δ(R_final) ≤ |C_fin|-1`,
    and otherwise `Δ(R_final) = |C_final|` (from UC1--UC3), at which point
    `hcount` (the `|C_final|` vertices of degree `< |C_final|`) and the
    regularity data of `G_final` feed Corollary 10.13, here taken in the
    *instantiated* form `hcor` (the top-level assembly discharges it from
    `GKOStatement` via `optcol_corollary_even` for the given `n`), giving
    `R_final.Colorable |C_final|`.
  * `s12_finish_B` (Type B): the Hall-based finishing
    (`exists_finishing_hall_of_margins`, with the Hall data `7δn ≤ |C_fin|`,
    `|U| ≤ δn`, `|C_w| ≤ δn`, `|{w : c ∈ C_w}| ≤ δn`, `d_{R_final}(w) + |C_w| ≤
    |C_final| - 1` and the covering condition on `U`).
  `S12Out`'s field `hUC4` was changed to take the *disjunction*
  `(∀ v ∈ V^{(n-1)}, v ∉ S₁) ∨ |U| ≤ (1-10ε)n` as its hypothesis, so that it is
  available both in Type A₁ (first alternative) and in Type B (second, where
  `|U| ≤ 2δn`); `s12_finish_A1`/`_A2` pass `Or.inl`.

  REMAINING for the assembly: the core's `UC1`--`UC4`/`hcount` (see part 15 for
  the `𝓜_prev^*`/singleton subtlety and the fast-iteration recipe), and then
  Step 1 (the constant hierarchy + `largeEdgeThmStatement_of_deep`) and the
  numeric discharge of all the hypotheses of `S12Margins`, `s12_core` and the
  three finishers.


* SESSION NOTE (current stretch, part 17) -- **THE §12 CORE IS COMPLETE**.
  `Submission/EFL/S12Core.lean` (1366 lines, sorry-free, in the cone) now
  contains the FULL proof of `s12_core`: from the Step-1--Step-5 data it
  produces `Mprev : Fin n → Set 𝓗`, `R_final`, `𝓗fin` together with every field
  of the structure `S12Out` (decomposition `(eqn:h_final)`, deficit bound
  `(eqn:deficit)`, degree identity `(eqn:deg_h_final)`, the bounds UC1--UC4 and
  the count of the `|C_final|` vertices of smaller degree).  Nothing in §12
  remains except **Step 1** and the **numeric discharge of the hypotheses**
  (see the plan at the end of this note).

  The two new ideas that made the core work:
  * **The starred family `𝓜_prev^*`.**  The paper's `m(w)` counts the matchings
    of `𝓜_prev^* = 𝓜_diff ∪ 𝓜_hm ∪ 𝓜_main^* ∪ 𝓜_buff` (where `𝓜_main^*` keeps
    the *singleton edges* produced by the nibble in `𝓗_reg`) that do **not**
    cover `w`.  The singleton-free family `prevFam` of `S12Mprev.lean` must
    therefore be replaced, for the degree estimates only, by
    `Mstar : ↥C_prev → Set (Set (Fin n))` which is `N j` on `C_main` and
    `prevFam` elsewhere (`nonsing (Mstar i) = prevFam … i.1`, which is what
    makes `s12_deg_h_final`'s `hfin`/`hdisj` work).  The singleton correction
    `hsingle` of `s12_deg_h_final` is then *non*-trivial and is supplied by the
    new conjunct of `NibbleStatement` (see below).
  * **`NibbleStatement`'s new singleton bookkeeping.**  `NibbleStatement`
    (S12Step6.lean consumes it as `h6₂₃ : ∀ w, #{i : {w} ∈ N i} ≤ n - 3 - d_𝓗(w)`)
    now records the faithful form of NB1: the matchings `N i` use *distinct
    copies* of each singleton edge of `𝓗'`, i.e.
    `#{i : {w} ∈ N i ∧ {w} ∉ M i} ≤ 𝓗'.singles w`; combined with `𝓗' ≤ 𝓗_reg`
    this gives `hsingle`.

  Also new in this stretch:
  * `s12_step5` / `s12_step5_inst` / `IsS12Step5` gained the **per-vertex** bound
    `∀ u ∈ U, #{c ∈ C_huge ∪ C_med : u ∉ V(M_c)} ≤ 1` (unconditional: in the
    perfect-coverage case the set is empty); `S12Step7Result` gained the
    analogous conjunct for `C_buff` (`∀ u ∈ U, #{c ∈ C_buff : u ∉ V(M_c)} ≤ 1`,
    proved from `(hGnear hUc).1`).  These are exactly the `hnp`/`hnp'`/`hnp''`
    hypotheses of `s12_mbound`.
  * `s12_uc` (S12Step9.lean) now takes `hm0` as an *implication* in its
    conclusion (its third component is `(∀ v ∈ Vn1, miss v = 0) → UC4`), so
    that UC2/UC3 can be derived without it; `s12_uc3_count`'s `hmiss` is now
    `(Vn1 ∖ V(M i)).ncard ≤ 1` (the `𝓜_diff`-matchings miss all of `V^{(n-1)}`).
  * `s12_step5_pack`/`s12_step5_pack_gen` now take the absorber `R₁` in the form
    `< bR₁_small : IsAbsorber … ρ_abs ζ ξ>` with `ζ + 3γ/2 ≤ 2γ` instead of
    `(10ξ)`.  Reason: `R₁ = R_abs ∖ ⋃𝓜_diff` is obtained from the Step-2
    absorber by **Observation `obs:del_absorber`(ii)**, which increases `γ` by
    the deletion parameter (here `1/n`, since `|C_diff| ≤ 1`), so R₁ is a
    `(10ξ + 1/n)`-absorber, never exactly `(10ξ)`; the assembly must therefore
    pass `ζ := 10ξ + 1/n`.

  LEAN LESSONS (this stretch):
  * Set-builder **shadowing**: in `{i | u ∉ f (g i)}` the `i` inside the
    set-builder is bound, so `rw [h] at hi` for a hypothesis `hi : i ∈ {…}`
    with a *free* `i` fails ("pattern not found").  Cure: first
    `have hi' : <unfolded predicate with the free i> := hi`, then rewrite `hi'`.
  * `rw [X.mpr h, …]` can fail with "unknown constant `X.mpr`" even though
    `exact X.mpr h` works; if that happens, state the equality in a `have`
    (or define a local lemma, as with `sdiff_eq_empty_of_subset`).
  * `Set.mem_union` works as a `rw` lemma but `Set.mem_union.mp` does not exist
    in this Mathlib; use `rw [Set.mem_union] at h; rcases h with …`.
  * `tauto` on a *huge* local context costs tens of minutes (it took S12Core
    from 20 s to > 50 min); replace it by explicit `Finset.mem_union.mp`
    case splits.  `set_option maxHeartbeats` raised to `64000000` is equally
    fatal: keep the file's default.
  * `omega` cannot see `x ∈ ↑s` for a `Finset` `s` (the `Finset.card_eq_zero`
    rewrite must be applied to a *fresh* `have`, not to the goal).

* SESSION NOTE (current stretch, part 18) -- **the assembly module
  `Submission/EFL/S12Final.lean` is started** (sorry-free, in the cone).
  * `card_finalColoursAt_le`: **`hCwLarge`** of `s12_core`, i.e.
    `|C_w| ≤ 2n/r₀` for `C_w = {c ∈ C_final : V(φ⁻¹(c)) ∋ w}`.  For every
    colour of `C_w` pick an edge of its class through `w`; the chosen edges are
    distinct (distinct colour classes are edge-disjoint) and of size `> r₀`, so
    they inject into `{e ∈ 𝓗_large(r₀) : w ∈ e}`, whose cardinality is
    `hdeg (𝓗.largeEdges r₀) w ≤ 2n/r₀` (`hdeg_largeEdges_le`, S12Numeric).
    Instances: `card_finalColoursAt_le_of_T1` (Type A: `C_w = ∅`) and
    `card_finalColoursAt_le_of_T2` (Type B: (T2) + `large_nonhuge_of_buff_union_final`).
  * `one_le_card_Cfinal`: `1 ≤ |C_final|` from `IsS12Colours.card_final_ge`
    (`|C_final| ≥ (ρ - 15√γ)n`) whenever `30√γ ≤ ρ` and `ρn ≥ 2`; and
    `one_le_rho_eps_mul` (`1 ≤ ρεn/4`), i.e. the two numeric hypotheses `hk1`,
    `hnum` of `s12_finish_A1`/`_A2`.
  * **`s12_chain`**: the middle of the assembly.  It derives the huge/medium
    size bounds (`huge_class_inter_U_le`, `hCmed_vertex`), the reservoir degree
    bound outside `U` (`degAt_Rres_le_of_notMem_Vplus`) and then chains
    `s12_step5_pack_gen` (Step 5) with `s12_core` (Steps 8/9), producing the
    final data `𝓜_prev`, `R_final`, `𝓗_final` and the whole structure `S12Out`.
    Its hypotheses are exactly the Step-1--Step-4 data plus `S12Margins` and the
    four numeric conditions `hCwLarge`, `hUCnum1`, `hUCnum2`, `hdeficitNum`.

  * A detail for Step 1 that is easy to get wrong: in the Type A case the
    maximality of `C_main` needs `|C_large| ≤ D = ⌊(1-ρ)(n-1)⌋` and `IsTypeA`
    only gives `|C_large| ≤ |C₁| ≤ (1-σ)n` with `C₁` the colour set of
    `NonExtremalColouring`.  The paper's hierarchy has `ρ ≪ σ` (NOT `σ ≪ ρ`:
    the order is `… ≪ γ₁ ≪ ε₁ ≪ ρ₁ ≪ σ ≪ δ ≪ …`), so the required numeric
    condition is `(1-σ)n + 1 ≤ (1-ρ)(n-1)`, i.e. `(σ-ρ)n ≥ ρ - 2`, which holds
    for `n ≥ 4/σ` as soon as `ρ ≤ σ/2`.  The same choice of `ρ` must leave room
    for `hUCnum2 : 2n/r₀ ≤ ρεn/4` (`r₀ ≥ 8/(ρε)`) and
    `hmargB : 2ρ(n-1)+1 ≤ εn` (`2ρ < ε`).

  * `s12_main_A1`: the **Type A₁ pipeline end to end** (modulo the numerics):
    `s12_chain` followed by `s12_finish_A1`, giving `χ'(𝓗) ≤ n` from the
    Step-1--Step-4 data, `S12Margins`, the two type-specific inputs (T1) and
    `V^{(n-1)}(𝓗) ∩ S₁ = ∅`.  The analogous wrappers for A₂ and B must derive
    the finishers' remaining hypotheses **inside** the wrapper, since they
    mention the *produced* `R_final`: for B, `hUcov` is
    `R_final ⊆ R_res ⊆ incidentTwo 𝓗 U` (the absorber is contained in `G'`),
    `hCw` follows from `hCwLarge` (`2n/r₀ ≤ δn`), `hCcol` from (T2)
    (`|V(φ⁻¹(c))| ≤ βn ≤ δn`), `hC` from `card_final_ge` and `hdeg` from
    UC1--UC4 together with (T2); for A₂, `hreg`/`hdelta` come from
    `s12_lowerRegular_final` (S12Step8r) applied to the `R_reg` part of the
    Type A₂ reservoir, and `hcor` from `GKOStatement` via `optcol_corollary_even`.

  So the only things left are: **Step 1** (choose the constants; obtain `φ` and
  the Type A/B alternative from `largeEdgeThmStatement_of_deep hMR hK` via
  `isTypeA_exists_of_nonExtremal`/`isTypeB_exists_of_extremal`; derive
  `IsS12Colours` by `s12_step3_typeA`/`_typeB`, the reservoir by
  `s12_step2_typeA1`/`_typeA2`/`_typeB`, `IsS12Step4` by `s12_step4_inst`, and
  the sharp absorber `R₁` by `IsAbsorber.delete` from the Step-2 absorber with
  `α = 1/n`), the **numeric discharge** of the hypotheses of `s12_chain`
  (`S12Margins`, `hCwLarge` -- now a theorem --, `hUCnum1`, `hUCnum2`,
  `hdeficitNum`, `hS_big`), and the **`∃ N₀` glue** wrapping the case split
  (A₁/A₂/B) with `s12_finish_A1`/`_A2`/`_B`.

* SESSION NOTE (current stretch, part 19) -- **§12 STEP 1 (the constant
  hierarchy) IS DONE; the per-type numeric parameter choice is the last piece.**
  New cone modules:
  * `Submission/EFL/S12Step1Full.lean`:
    - `isTypeA_of_nonExtremal_medLarge` / `isTypeB_of_extremal_medLarge`:
      **Theorem 6.7 applied to `medLarge 𝓗 r₁` IS the §12 hypothesis** (up to
      reordering the existential quantifiers, which is all that is needed,
      since `LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ 𝓖` asks for a colouring of
      `𝓖` and `IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ` asks for one of `medLarge 𝓗 r₁`;
      taking `𝓖 = medLarge 𝓗 r₁` the two fields match literally).  No
      restriction (`Coloring.restrict`) or transport is needed for §12 -- the
      restriction in `S12Step1.lean` is only for the "colouring of all of `𝓗`"
      formulation.
    - `s12_step1 (hMR) (hK)`: from `largeEdgeThmStatement_of_deep` it produces
      the whole hierarchy `γ₂ ≥ δ ≥ σ ≥ γ₁ ≥ β`, `r₁`, `r₀`, `N₀` with the
      *concrete choices* `γ₂ := 10^{-24}`,
      `δ := min δ₀ (γ₂/2)`, `σ := min σ₀ (δ/2)`,
      `γ₁ := min γ₁₀ ((σ/10^7)^2)`, `β := min β₀ (γ₁/2)`,
      `r₁ := max R₁ (max 10 ⌈32/β⌉₊)`,
      `r₀ := max R₀ (max 2 (⌈max (4r₁/γ₁) (r₁/β)⌉₊ + 2))`,
      and the guarantees `32 ≤ βr₁`, `r₁ < β(r₀-1)`, `r₁ < (γ₁/4)(r₀-1)`
      (for `DegreeMargins.hβr1 : 16 ≤ (β/2)r₁`, `EP2num_le` and
      `overlap_le_gamma_mul`), plus, for every `n ≥ N₀`,
      `∃ φ, IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ ∨ IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ`.
    The sizes of the constants are dictated by the *binding* constraints
    `1000·(3γ/2) ≤ ρ_abs ε` (`HugeMargins.hγε`), `15√γ ≤ ρε/2` (`hUCnum1`),
    `30√γ ≤ ρ` (`one_le_card_Cfinal`), `2ρ < ε` (`hmargB`) and `ρ ≪ σ`
    ((T1), Type A only).  With `ε = 10^{-4}` these give
    `γ ≤ 10^{-20}` (hence `γ₂ := 10^{-24}`) and, for Type A with `ρ = σ/2`,
    `γ₁ ≤ (σ/10^7)^2`.  The *type-dependent* parameters are chosen per case:
    `γ := γ₁`, `ρ := σ/2` for Type A (`γ := γ₂`, `ρ := 10^{-5}` for Type B),
    `ε := 10^{-4}`, `ρ_abs := ρ/2`, `ξ := min(γρ_abs, β, γ, ρε)/10^4`,
    `κ := 1/2`.
  * `Submission/EFL/Comm/S12NumericArith.lean`: verbatim ports (narrow imports)
    of the three commons arithmetic lemmas proved by the fleet this stretch:
    `Commons.Analysis.Real.one_sub_mul_add_one_le` (the (T1) inequality
    `(1-σ)n+1 ≤ (1-ρ)(n-1)`), `floor_mul_sub_one_add_le` (the `hS₂num`
    inequality) and `le_floor_mul_sub_one` (`n/2 ≤ ⌊(1-ρ)(n-1)⌋`).

* SESSION NOTE (current stretch, part 20) -- **the per-type numeric parameter
  lemma is written, split into "structure" (done) and "thresholds" (delegated).**
  New cone module `Submission/EFL/S12Params.lean`:
  * **`S12Margins_of`** (sorry-free): given the *constant* hierarchy
    (`0 < β`, `0 < γ`, `0 < ρ ≤ 1/4`, `0 < ρ_abs ≤ 1`, `0 < ε`, `1000ε ≤ 1`,
    `β ≤ γ ≤ 1`, `γ ≤ 2ε`, `3γ ≤ ε`, `2ρ ≤ ε/2`, `1000·(3γ/2) ≤ ρ_abs ε`,
    `10√γ < 3ε`, `16 ≤ (β/2)r₁`, `r₁ ≤ β(r₀-1)`, `2r₁ ≤ γ(r₀-1)`) together with
    the `n`-large facts (`2 ≤ εn`, `8 ≤ βn`, `6 ≤ βn`, `24 ≤ (β/2)n`,
    `100 ≤ εn`, `8 ≤ n`, `32/β² ≤ γn/2`, `r₁ < βn/4`, `2000 ≤ (3γ/2)ρ_abs n`,
    `2ρ(n-1)+1 ≤ εn`, `(β/2)n/2 ≤ (1-ρ)(n-1)`, `2 ≤ 10√γ D`), it produces
    `ξ := min (min (γρ_abs) β) (min γ (ρε)) / 10^4` and `κ := 1/2` with
    `S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ`.  The `ξ`-conditions
    (`8ξ ≤ β/2`, `10ξ ≤ γ/2`, `4000ξ ≤ (3γ/2)ρ_abs`) are immediate from the
    definition, and the `Dparam`-conditions come from `n_le_two_Dparam`,
    `two_thirds_beta_le`, `EP2num_le`, `overlap_le_gamma_mul`,
    `D'param_ge_half` (S12Numeric) and `le_floor_mul_sub_one`,
    `floor_mul_sub_one_add_le`, `one_sub_mul_add_one_le` (the ported commons
    arithmetic).
  * **`exists_S12Margins`**: the wrapper.  For a constant hierarchy
    (`β ≤ γ ≤ 1`, `ρ ≤ 1/4`, `2ρ ≤ ε/2`, `1000·(3γ/2) ≤ ρ_abs ε`, plus the two
    size conditions linking `r₀` to `r₁, β, γ`) it produces `ξ` and `N` with
    `S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε (1/2)` for every `n ≥ N`.  The
    `n`-large facts come from the fleet's commons lemma
    `Commons.Analysis.Real.exists_thresholds_hierarchy_rho_eps` (which
    **corrected** an earlier, false draft of mine: the hypothesis `2ρ ≤ ε/2` is
    essential -- without it `2ρ(n-1)+1 ≤ εn` fails for large `n`; the prover
    supplied a counterexample and the fixed version), ported verbatim into
    `Submission/EFL/Comm/S12NumericArith.lean`.
  * So the per-type parameter choice is now: Type A -- `γ := γ₁`, `ρ := σ/2`,
    `ε := 10^{-4}`, `ρ_abs := ρ/2`; Type B -- `γ := γ₂`, `ρ := 10^{-5}`,
    `ε := 10^{-4}`, `ρ_abs := ρ/2`; each satisfying the constant hypotheses of
    `exists_S12Margins` (with `s12_step1`'s guarantees
    `γ₁ ≤ (σ/10^7)²`, `γ₂ ≤ 10^{-24}`, `32 ≤ βr₁`, `r₁ < (γ/4)(r₀-1)`,
    `r₁ < β(r₀-1)` and `2ρ ≤ ε/2`).
  * LEAN LESSON: inside a context containing `Real.sqrt`/`Dparam`/many
    hypotheses, a bare `linarith` can hit the heartbeat limit even on trivial
    goals; use `linarith only [h1, h2]` (and pre-derive products with
    `mul_le_mul_of_nonneg_right`) instead.  A failing proof can also produce a
    spurious "timeout at whnf" on the *statement* line.

* SESSION NOTE (current stretch, part 21) -- **BOTH call sites of
  `exists_S12Margins` ARE DONE** (`Submission/EFL/S12Params.lean`, sorry-free,
  in the cone):
  * `S12Margins_typeA`: with `γ := γ₁`, `ρ := σ/2`, `ρ_abs := σ/4`,
    `ε := 10⁻⁴`, `κ := 1/2`, from `γ ≤ (σ/10⁷)²`, `σ ≤ 10⁻⁵`, `0 < β ≤ γ ≤ 1`,
    `32 ≤ βr₁`, `r₁ ≤ β(r₀-1)`, `r₁ < (γ/4)(r₀-1)` it produces `ξ` and `N` with
    `S12Margins n r₁ r₀ β γ (σ/2) (σ/4) ξ (1/10⁴) (1/2)` for all `n ≥ N`,
    together with the downstream side conditions `30√γ ≤ ρ`, `ξ + 15√γ ≤ ρε/2`,
    `8 ≤ ρεr₀`, `3γ ≤ √γ` (and `ρ ≤ σ/2` is the definition of `ρ`).
  * `S12Margins_typeB`: the same with `γ := γ₂ ≤ 10⁻²⁴`, `ρ := 10⁻⁵`,
    `ρ_abs := 1/(2·10⁵)`, `ε := 10⁻⁴` (no `σ`-side condition: Type B has no
    (T1) argument), the side conditions `30√γ ≤ ρ`, `ξ + 15√γ ≤ ρε/2`,
    `8 ≤ ρεr₀`, `3γ ≤ √γ`.
  These are exactly the inputs the assembly needs: `s12_chain`'s `hm`, plus
  `ρ ≤ σ/2`/`30√γ ≤ ρ`/`ξ + 15√γ ≤ ρε/2`/`8 ≤ ρεr₀` (which give `hUCnum1`,
  `hUCnum2` and `one_le_card_Cfinal`).

* SESSION NOTE (current stretch, part 22) -- **what the Type A₁ chain still
  needs (found while starting the one-call assembly).**  Wiring
  `s12_step1` -> `S12Margins_typeA` -> `s12_step2_typeA1` -> `s12_step3_typeA`
  -> `s12_step4_inst` (+ the sharp `R₁`) -> `s12_chain` -> `s12_main_A1` needs,
  beyond the numerics already available, exactly one non-trivial arithmetic
  identity: the paper's `(eqn:rs)`, i.e.
  `|S| ≥ (1-ρ)n + 5εn` when `|U| > (1-10ε)n`, for the Type A₁ defect set
  `S = U ∖ V^{(n-1)}(𝓗)`.  That reduces to
  `|V^{(n-1)}(𝓗)| ≤ (ρ - 15ε)n`, which must come from `¬ IsFull 𝓗 ρ ε`
  (`IsFull`'s second conjunct bounds `VeqNat 𝓗 (n-1) = {v : d_G(v) = n-1}`,
  while `S` uses `Vdeg 𝓗 (n-1) = {v : d_𝓗(v) = n-1}`).
  **NEW PREREQUISITE (not yet in the repository):**
  `Vdeg 𝓗 (n-1) ⊆ VeqNat 𝓗 (n-1)` for a *linear* `𝓗` with all edges of size
  `≥ 2`.  Mathematics: if `d_𝓗(v) = n-1` then every edge through `v` has
  exactly two vertices -- otherwise the `n-1` sets `e ∖ {v}` (pairwise
  disjoint by linearity, each of size `≥ 1`) would cover more than the `n-1`
  vertices of `V ∖ {v}`.  Proof route: the incidence set
  `I := E.toFinset.sigma (fun e => (e ∖ {v}).toFinset)` (with
  `E := {e ∈ 𝓗 | v ∈ e}`, `|E| = n-1`) injects into `V ∖ {v}` via `(e,w) ↦ w`
  (linearity), so `I.card ≤ n-1`; on the other hand each fibre has `≥ 1`
  element, so `I.card ≥ |E| = n-1`.  Hence `I.card = n-1` and every fibre is a
  singleton, i.e. `|e ∖ {v}| = 1` for every edge `e` through `v`, so
  `|e| = 2` and `d_G(v) = d_𝓗(v) = n-1` (`hdeg_eq_degAt`, DegreeBounds).
  In Type A₂/B one takes `S = U` instead, so `(eqn:rs)` is then immediate from
  `IsFull`'s first conjunct / `EP3`.

* SESSION NOTE (current stretch, part 23) -- **`V^{(n-1)}(𝓗) ⊆ VeqNat 𝓗 (n-1)`
  IS PROVED** (`Submission/EFL/S12Step1Full.lean`, sorry-free, in the cone):
  * `Vdeg_pred_subset_VeqNat_of` (glue): given the counting fact
    `∀ v, d_𝓗(v) = n-1 → ∀ e ∈ 𝓗, v ∈ e → e.ncard = 2`, the inclusion follows
    because the edges of `𝓗` through `v` are then exactly the 2-edges through
    `v` (`hdeg_eq_degAt`).
  * `Vdeg_pred_subset_VeqNat`: the inclusion for linear `𝓗` with all edges of
    size `≥ 2`, from the fleet's commons lemma
    `Commons.Combinatorics.Hypergraph.ncard_eq_two_of_mem_ncard_pred`
    (proved and committed this stretch; it reduces to the companion
    `eq_univ_pairs_of_degree`), ported verbatim into
    `Submission/EFL/Comm/NcardEqTwo.lean` (narrow imports
    `Mathlib.Data.Set.Card.Arithmetic`, `Mathlib.Tactic.Ring`,
    `Mathlib.Order.Basic`; note `Mathlib.Tactic.Omega`'s olean is *not* built
    in this toolchain).
  * Consequence: `(eqn:rs)` for Type A₁ is now available -- from
    `¬ IsFull 𝓗 ρ ε` and `|U| > (1-10ε)n` one gets
    `|V^{(n-1)}(𝓗)| ≤ |VeqNat 𝓗 (n-1)| < (ρ-15ε)n`, hence
    `|S| = |U| - |U ∩ V^{(n-1)}| ≥ |U| - |V^{(n-1)}| > (1-ρ+5ε)n`.  (The
    remaining assembly step is to write that three-line calculation, plus the
    same for the A₂/B cases where `S = U`.)
  * Also this stretch: `S12Margins_typeA` / `S12Margins_typeB` (the two call
    sites of `exists_S12Margins`) -- see part 21.

* SESSION NOTE (current stretch, part 24) -- **`(eqn:rs)` IS PROVED FOR ALL
  THREE TYPES** (`Submission/EFL/S12Step1Full.lean`, sorry-free, in the cone):
  * `S_big_typeA1`: for `S = U ∖ V^{(n-1)}(𝓗)`, `¬ IsFull 𝓗 ρ ε` and
    `|U| > (1-10ε)n` (which establishes `IsFull`'s *first* conjunct, so the
    second one fails) give `|V^{(n-1)}(𝓗)| < (ρ-15ε)n` via
    `Vdeg_pred_subset_VeqNat`, and `|U| = |S| + |V^{(n-1)}|` (as
    `V^{(n-1)} ⊆ U`) turns that into
    `|S| > (1-ρ+5ε)n ≥ (1-ρ)n + 5εn`.
  * `S_big_typeA2`: with `S = U` it is the pure inequality `15ε ≤ ρ`.
  * `S_big_typeB`: with `S = U` it is *vacuous* -- `EP3` gives `|U| ≤ 2δn` and
    the hierarchy has `2δ < 1 - 10ε`.
  These are exactly the `hS_big` hypotheses of `s12_step5_pack_gen` /
  `s12_chain` (and `s12_step4_inst`'s `S`-hypotheses via `IsS12Step4`).

  REMAINING for the whole project (in order):
  1. **Step 1 + the numeric glue** (see part 14 for the plan): choose the
     constant hierarchy, obtain `φ` and `IsTypeA ∨ IsTypeB` from
     `largeEdgeThmStatement_of_deep hMR hK` (`s12_step1`-style plumbing already
     exists in `S12Step1.lean`: `isTypeA_exists_of_nonExtremal`,
     `isTypeB_exists_of_extremal`), then `s12_step2_typeA1/_typeA2/_typeB`,
     `s12_step3_typeA/_typeB`, `s12_step4_inst`, `s12_step5_pack_gen`,
     `s12_steps67` (S12Assem) and `s12_core`, and finally one of
     `s12_finish_A1/_A2/_B`.  The type split is: Type A ∧ ¬IsFull -> A₁,
     Type A ∧ IsFull -> A₂ (uses `exists_regularising_reservoir` /
     `Lemma 11.3` + `optcol_corollary_even`), Type B -> B (Hall finishing).
  2. `eflStatement_of_bigEdges` + `eflStatement_iff_threshold` to reach
     `theorem_1_1`.
  3. The eight deep inputs (`MolloyReedStatement`, `KahnStatement`,
     `AKSStatement`, `GKOStatement`, `EGJStatement`/`SparseEGJStatement`,
     `NibbleStatement`, `LeftoverStatement`, `lem:embed`) -- these are the
     actual obstructions to an unconditional `theorem_1_1`.

-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

/-- Placeholder marker: this file is pure documentation; it only re-exports the
verified infrastructure.  All propositions below are the already-proven API
statements, gathered here so that `import Submission.EFL.Roadmap` provides the
whole verified development in one module. -/
theorem roadmap_colorable_iff_chromaticIndex (n : ℕ) (𝓗 : Hypergraph (Fin n)) :
    (∃ k : ℕ, 𝓗.Colorable k) → (𝓗.chromaticIndex ≤ n ↔ 𝓗.Colorable n) := by
  intro h
  exact Hypergraph.chromaticIndex_le_iff_colorable 𝓗 h (k := n)

theorem roadmap_reduction :
    (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      (∀ e ∈ 𝓗, HasTwoVertices (e : Set (Fin n))) → 𝓗.chromaticIndex ≤ n) →
    eflStatement := by
  intro h
  exact eflStatement_of_bigEdges h

end ErdosFaberLovaszConjecture

/-!

## SESSION NOTE (the Type A branch of §12 is assembled)

**New cone modules** (all imported by `Submission.lean`, sorry-free):

* `Submission/EFL/Comm/TwoMulLeRpowLog.lean` — port of the commons threshold
  `∃N, ∀n≥N, 2n+2 ≤ n^{log n}` with minimal imports.
* `Submission/EFL/S12ANum.lean` — `structure S12ANum n r₁ r₀ β γ σ ξ ρabs`
  bundling ALL the numeric side conditions of the Type A branch with
  `ρ = σ/2`, `ε = σ³/10⁴²`, `κ = 1/2` (and `ρ_abs = σ/2` for A₁, `σ/4` for A₂),
  plus `exists_S12ANum` producing `ξ` and the threshold `N` from
  `γ ≤ σ¹⁰/10²⁵⁰`, `32 ≤ βr₁`, `r₁ < (γ/4)(r₀-1)`; the helpers
  `sqrt_gamma_le`, `gamma_le_pow_mul`, `sqrt_le_pow_mul`, `xi_le_pow_mul`
  are the (private) numeric workhorses.
  NOTE: `S12Step1Full.lean`'s `s12_step1` now produces `γ₁ ≤ σ^10/10^250`
  (instead of `(σ/10^7)^2`), which is what makes `√γ ≪ ρε` and `ε^{1/3} ≪ ρ`
  compatible.
* `Submission/EFL/S12MainA.lean` — `IsAbsorber.delete_step4` (the sharp
  absorber `R₁ = R_abs ∖ ⋃𝓜_diff`, from `obs:del_absorber` + the `∪ C_diff`
  bookkeeping), `s12_branch_A1` (Steps 3–10 in the non-full case),
  `exists_cvFinset_card_le` (`|𝓥| ≤ n^{log n}` for large `n`) and
  `s12_A1_main` (the same with the threshold `N`, the constants as parameters).
* `Submission/EFL/S12MainA2.lean` — `s12_lowerRegular_final_gen` (the
  robustness step with the target parameter), `s12_finish_A2_gen` (Case A₂:
  Vizing or Corollary 10.13, with `p`, `ζ`, `η` as parameters and WITHOUT the
  spurious `hVn1` hypothesis), `s12_to_S12Out` (the Steps 5–9 chain extracted
  from `s12_main_A1`), `sqrt_fifteen_sqrt_gamma_le`, and **`s12_branch_A2`**
  (the full Type A₂ branch).  The A₂ numerics use `η = σ/10³⁰` for the
  lower-regularity parameter of `G_final[U]` and `ζ = σ/10¹⁴` for the target
  (`cor:optcol` with `p = ρ/4`).

**Also refactored**: `DegreeMargins` no longer contains `hmargB`; the
inequality `2ρ(n-1)+1 ≤ εn` is now an explicit conjunct of the *Type B*
disjunct of the `hres` disjunction in `regularising_lemma_core`,
`regularising_lemma`, `s12_step6`, `s12_core`, `s12_chain`, `degAt_Rres_le_of_notMem_Vplus`
and `s12_steps67`.  This is what allows the Type A₂ branch to use `ρ ≫ ε`
(the paper's hierarchy) while Type B keeps `ρ ≪ ε`.  `exists_S12Margins` lost
its `hρlt`-dependency only in `S12Margins_of` (which no longer needs `hρlt`).

**Remaining**: `s12_A2_main` (threshold version of the A₂ branch, using
`s12_step2_typeA2` + `optcol_corollary hGKO`), the Type B branch, and the final
assembly; details in `Submission/EFL/S12MainA2WIP.txt`.

## SESSION NOTE: §12 IS COMPLETE -- THE FINAL ASSEMBLY (`eflStatement_of_deep`)

**New cone modules** (all imported by `Submission.lean`, sorry-free):

* `Submission/EFL/S12A2Main.lean` — **`s12_A2_main`**, the threshold form of the
  Type A₂ branch: from the constant hierarchy it produces `ξ` (`exists_S12ANum`
  with `ρ_abs = σ/4`), the threshold of `s12_step2_typeA2 (ρ := σ/2)` and of
  `optcol_corollary hGKO (η := 22·σ³/10⁴²) (ε := σ/10¹⁴) (p := (σ/2)/4)`
  (whose numeric hypotheses are proved directly from `σ ≤ 10⁻²⁴`), then calls
  `s12_branch_A2`.  The `IsReservoirTypeA2` output is unpacked to recover
  `R_abs` with its *lower regularity* (`hRabs_low`), which is what
  `s12_branch_A2` needs.
* `Submission/EFL/S12BNum.lean` — **the Type B numerics**: the structure
  `S12BNum n r₁ r₀ β γ δ ξ` with `ρ = ρ_abs = 10⁻⁵`, `ε = 10⁻⁴`, `κ = 1/2`
  (note `ρ_abs = ρ`: in Type B one call of `s12_step2_typeB` produces the
  reservoir *and* the absorber with the same parameter, so no
  `IsReservoirTypeA2`-style splitting is needed), plus `exists_S12BNum`
  producing `ξ`, `N` from the `s12_step1` hierarchy
  (`γ ≤ 10⁻²⁴`, `δ ≤ 10⁻²⁴`, `σ ≤ δ`, `γ₁ ≤ σ¹⁰/10²⁵⁰`, `β ≤ γ₁`,
  `32 ≤ βr₁`, `r₁ ≤ β(r₀-1)`, `r₁ < γ₁(r₀-1)/4`).  The fields include
  `hmargB` (the `2ρ(n-1)+1 ≤ εn` conjunct of the Type B disjunct), `hnum3`
  (the nibble's C1/C3 condition, proved pointwise from `h.dk2`), `hδr₀`
  (`4 ≤ δr₀`, proved from `hr₀big`: `4r₁ < γ₁(r₀-1) ≤ σ(r₀-1) ≤ δr₀`), and
  the `|C_final|`-lower-bound input `hCfin : 14δ + 15γ^{1/2} ≤ ρ`.
* `Submission/EFL/S12ChainGen.lean` — **`s12_chain_gen` / `s12_to_S12Out_gen`**:
  copies of `s12_chain` / `s12_to_S12Out` in which the size bounds
  `hbigsize : ∀ c ∈ Chuge, |V(φ⁻¹(c)) ∩ U| ≤ εn` and
  `hmedsize : ∀ c ∈ Cmed, |V(φ⁻¹(c))| ≤ (3γ/2)n` are *hypotheses* instead of
  being derived from `φ.SingletonClassesForHuge β`.  In Type A they follow from
  EP1 (`huge_class_inter_U_le`); in Type B from `(6.7:b)`
  (`∀ c, AssignedToHuge β c → classVertexCount c ≤ δn`, which gives
  `δn ≤ εn`).  This is what makes the Steps 5--9 chain usable in all three
  types.
* `Submission/EFL/S12MainB.lean` — **the Type B branch**:
  * `card_filter_finalColoursAt` — the colour-side Hall count
    `#{w : c ∈ C_w} = |V(φ⁻¹(c))|` for `c ∈ C_final`
    (`Finset.univ.filter … = (matchVert (colourFam φ c)).toFinset` then
    `Set.ncard_eq_toFinset_card'`;  NB the plain `ncard_eq_toFinset_card` has a
    `Finite` autoParam whose `toFinset` is not syntactically the `Set.toFinset`
    of the goal — use the primed version).
  * `IsS12Colours.card_med_diff_huge_le_bound` — `(eqn:bound_prev_colours)`
    `|C_med ∪ C_diff ∪ C_huge| ≤ γn + 32/β²` for a Step-3 output (it was
    previously only proved inside `exists_S12Colours_typeA`); needed by the
    Type B branch, which does not go through `s12_step3_typeA`.
    **LEAN PITFALL**: the *name* `card_med_diff_huge_le` inside the namespace
    `IsS12Colours` shadows the top-level one while the theorem is being
    elaborated (the current namespace is extended with the new name), so a
    recursive-looking resolution error appears; hence the `_bound` suffix.
  * **`s12_branch_B`** — Steps 3--10 in the extremal case: `s12_step3_typeB`
    → (EP3: `|U| ≤ 2δn`, no difficult class) so `C_diff = ∅`
    (`isS12Step4_of_Cdiff_empty` with `R₁ = R_abs = R_res`, `S₁ = S = U`) →
    the class-size bounds of Step 5 → `s12_to_S12Out_gen` → **Step 10 by the
    Hall finishing lemma with parameter `2δ`** (not `δ`): EP3 gives only
    `|U| ≤ 2δn`, so the finisher is called with `δ' := 2δ`, which requires
    `7·2δ n ≤ |C_final|` (from `(eqn:bound_prev_colours)`), `|C_w| ≤ 2δn`
    (from `2n/r₀` and `1 ≤ δr₀`), `#{w : c ∈ C_w} ≤ 2δn` (from
    `classVertexCount c ≤ βn ≤ 2δn`) and `2δ < 1 - 10ε` (UC4).  The defect set
    is `S = U`, so `(eqn:rs)` is vacuous (`S_big_typeB`).
  * **`s12_B_main`** — the threshold form, assembling `exists_S12BNum`,
    `s12_step2_typeB (ρ := 10⁻⁵)` and `exists_cvFinset_card_le`.
* `Submission/EFL/S12Assembly.lean` — **THE FINAL ASSEMBLY**:
  * `hasTwoVertices_iff_two_le_edgeSize` (`HasTwoVertices e ↔ 2 ≤ e.ncard`, via
    `Set.one_lt_ncard`; note `HasTwoVertices e = ∃ x, ∃ y, x ∈ e ∧ y ∈ e ∧
    x ≠ y` — a 5-tuple pattern, while `Set.one_lt_ncard` gives
    `∃ a, a ∈ e ∧ ∃ b, b ∈ e ∧ a ≠ b` — also a 5-tuple pattern);
  * **`eflStatement_of_deep hMR hK hNib hLeft hGKO : eflStatement`** — apply
    `s12_step1 hMR hK`, then case on `IsFull 𝓗 (σ/2) (σ³/10⁴²)` and dispatch
    to `s12_A1_main` (not full), `s12_A2_main` (full) and `s12_B_main`, and
    conclude with `eflStatement_of_bigEdges`.

**MODIFICATIONS OF EARLIER CONE FILES** (all rebuilt):
  * `exists_S12Colours_typeB` (S12Setup.lean) and `s12_step3_typeB`
    (S12Mprev.lean) now also return
    `∀ c, c ∉ Cmed → ¬ φ.AssignedToHuge β c → classVertexCount c ≤ βn`
    (the last conjunct of `IsTypeB`, i.e. the `hvert` input of the chain).
    This is needed because the `Cmed` produced by `s12_step3_typeB` is *not
    definitionally* `hB.2.choose`: `obtain ⟨-, -, …, hlast⟩ := hB` cannot even
    bind the `∃`-witness under a `-` pattern together with later components
    (the wildcard in the witness position breaks the anonymous-constructor
    flattening — bind it to a name instead), and `hB.2.choose_spec.…` has a
    `Cmed` that is not syntactically the one Step 3 returns.

**STATE OF THE PROJECT.**  Every step of the paper's §1--§12 is now
machine-checked and *sorry-free* in the cone, and the chain is assembled end to
end:

  `eflStatement_of_deep : MolloyReedStatement → KahnStatement →
     NibbleStatement → LeftoverStatement → GKOStatement → eflStatement`.

`Submission.theorem_1_1` is therefore exactly
`change eflStatement; exact eflStatement_of_deep ⟨…⟩` once the five **deep
input `Prop`s** are supplied.  Those `Prop`s are the remaining mathematical
obstructions:

* `MolloyReedStatement`, `KahnStatement` (used by `s12_step1` through
  `largeEdgeThmStatement_of_deep`);
* `GKOStatement` (Theorem 10.8 of the paper, used by `optcol_corollary`);
* `LeftoverStatement` (`lem:leftover`) and `NibbleStatement` (`lem:nibble2`).

Two of these are *provable in principle from the others* and are the natural
next targets (the paper proves them in §§7--9):

* `LeftoverStatement` from `KahnStatement` (+ `huge_edge_absorption` = Lemma
  7.3, already in the cone) + a probabilistic balancing argument;
* `NibbleStatement` from `SparseEGJStatement`/`EGJStatement` + `lem:embed`
  (the embedding lemma `lem:embed`, which is **not yet even stated** in the
  cone; it needs an API for hypergraphs on a *larger* vertex set).

**IMPORTANT FINDINGS ABOUT `LeftoverStatement`** (made while preparing its
proof; the statement will have to be repaired before it can be proved):
  1. It has **no linearity hypothesis**, but its proof uses **Kahn's theorem**,
     which needs `𝓗_rem` linear (`𝓗rem ⊆ 𝓗.edges`; the paper's ambient `𝓗` is
     linear).  A greedy list-colouring argument does *not* suffice: the lists
     `C(e)` have size `≤ γ²D/100` while `Δ(𝓗_rem) ≤ γ²D/20` and
     `|C_i| ≥ γ²D/10`, so only an asymptotically optimal list-colouring theorem
     (Kahn) works.
  2. It has **no `n`-large hypotheses**, but the proof needs them (Kahn's `D₀`,
     `n/t` vs `γn/4` in the Chernoff step, and `HugeMargins`-type conditions for
     Lemma 7.3).  The faithful statement should carry the paper's
     `0 < 1/n₀ ≪ 1/r, ξ ≪ γ ≪ ρ, ε ≪ 1` and `D ∈ [n^{2/3}, n]` explicitly
     (e.g. as an `∃ n₀` prefix, or by taking the `HugeMargins` data as a
     hypothesis).  If such a hypothesis is added, the *call site*
     (`s12_step7`, which has `hlin`, `hbig` and the ambient `S12Margins`
     available one level up) must be updated, and the extra hypotheses must be
     threaded through `s12_steps67`/`s12_core`/`s12_chain`/the three masts.
  3. The proof splits into: partition `Fin k` into `t = ⌈4/γ⌉` parts of size
     `≥ γ²D/10`; for each part a Kahn list-colouring of `𝓗_rem`; a random
     merging of the `t` colourings whose classes are all `< γn/2` (the
     probabilistic step, `Commons.Probability.Chernoff.*` +
     `Commons.Combinatorics.FiniteSampling.exists_finset_sum_close` for the
     independent-sampling form); and finally Lemma 7.3 with `𝓥 = {U, univ}`
     (the smallness alternative `AbsorbableBySmall`).
     NB `huge_edge_absorption` is stated for a plain `Hypergraph` and
     `Hypergraph.IsMatching`, whereas `LeftoverStatement` is stated for a
     `MultiHypergraph` whose singleton edges "are available in several copies"
     (`EdgeDisjointFam` only requires disjointness of the *non-singleton*
     parts) — the transport between the two worlds (via
     `MultiHypergraph.edgeSet`, `ofHypergraph`, `toFam`) is glue that the proof
     will need.

**NEW LEAN LESSONS** (this stretch):
  (a) `obtain ⟨-, Cmed, …⟩ := h` works but `obtain ⟨-, -, …⟩ := h` (two
      wildcards in a row, the first two being an `∃`-witness) silently fails to
      bind later components: name the witness.
  (b) A theorem named `IsS12Colours.foo` cannot (inside its own proof) call the
      top-level `foo`: use a different name or the fully qualified name.
  (c) `linarith`/`nlinarith` never multiply an inequality by a *monomial* that
      is not a hypothesis, and they treat `10^5` (a `HPow`) as an atom: supply
      every constant comparison as a separate `have … := by norm_num` and every
      multiplying factor (e.g. `Nat.cast_nonneg n`) explicitly.  When the goal
      is `a * n ≤ b * n` the right form is `mul_le_mul_of_nonneg_right`.
  (d) `pow_le_pow_of_le_one h0 h1 hn : a ^ m ≤ a ^ n` — the third argument is
      the *exponent* inequality `n ≤ m`; and `γ ≤ 1` from `√γ < 1` needs
      `pow_lt_one₀` (nlinarith cannot multiply two strict inequalities).
  (e) `Set.ncard_eq_toFinset_card'` is the version to use (the unprimed one has
      a `Finite` autoParam whose `toFinset` does not match `Set.toFinset`).
  (f) `rw [def_name]` works for a plain `def` (it uses its equation lemma) but
      only when the *pattern* `def_name …` occurs in the goal/hypothesis.


## SESSION NOTE: THE LEFT Sandbox -- `LeftoverProof.lean` (the first two steps of `lem:leftover`)

**New cone module** `Submission/EFL/LeftoverProof.lean` (imported by
`Submission.lean`, sorry-free).  It starts the formalisation of the paper's
Lemma `lem:leftover` from `KahnStatement` + `huge_edge_absorption` (Lemma 7.3),
and contains:

* **glue between multi-hypergraphs and hypergraphs**:
  `Hypergraph.pow2_idem` (`(G^(2))^(2) = G^(2)`),
  `MultiHypergraph.pow2_eq_edgeSet_pow2` (`𝓜.pow2 = (𝓜.edgeSet).pow2`, because
  the singletons have size one),
  `MultiHypergraph.incidentTwo_pow2`
  (`incidentTwo 𝓜.pow2 U = incidentTwo 𝓜.edgeSet U`, via the previous two and
  `unfold incidentTwo` — the `pow2`-rewrite does not fire through the `def`, so
  it must be unfolded first),
  `MultiHypergraph.isLinear_edges`, `MultiHypergraph.edges_isLinear_of_subset`.
  Note `𝓜.edges.IsLinear` / `𝓜.edgeSet.pow2` do **not** elaborate with dot
  notation (since `Hypergraph` is an `abbrev`): write `Hypergraph.IsLinear`,
  `Hypergraph.pow2` explicitly.
* **`exists_list_colouring_in_part`** — Kahn's theorem with `α = 1/2`,
  transported from `𝓖.Coloring (Fin c)` to an arbitrary colour set `ι` with a
  part `P : Finset ι` and forbidden lists `L e ⊆ P`: given the instantiated Kahn
  body for `D₀` (a hypothesis), `Δ(𝓖) ≤ D'`, edge sizes `≤ r`,
  `(3/2)D' ≤ |P|` and `|L e| ≤ D'/4`, there is `ψ : 𝓖.Coloring ι` with
  `ψ(e) ∈ P` and `ψ(e) ∉ L e`.  (The transport uses `Fintype.equivFin ↥P`
  composed with `finCongr`, and `Finset.card_le_card_of_injOn` for the lists.)
* **`exists_merged_colouring`** — the probabilistic merging: given `t`
  colourings `ψ j` with pairwise disjoint parts `P j`, classes of total size
  `≤ W` and the union bound
  `|ι|·2·exp(-τ²/(2(C(W/t+τ/3)))) < 1`, there is `pick : 𝓖 → Fin t` such that
  every class of `e ↦ ψ (pick e) e` has total edge size `≤ W/t + τ`.  This is
  the commons lemma
  `Commons.Combinatorics.BalancedColouring.exists_colouring_bounded_load`
  applied with `jof c :=` any part containing `c` (defined with `dif_pos` so
  that the *same* proof term is reused, otherwise the rewrite fails).

**The commons now also has** (proved by the fleet this stretch)
`Commons.Combinatorics.Partition.exists_colouring_parts_ge` (split a finite set
into `t` parts of size `≥ m` when `t*m ≤ |ι|`) and
`Commons.Combinatorics.BalancedColouring.exists_colouring_bounded_load`.

**REMAINING STEPS OF `lem:leftover`** (in order, all in the cone):

1. **The margins.**  The paper's `0 < 1/n₀ ≪ 1/r, ξ ≪ γ ≪ ρ, ε ≪ 1` and
   `D ∈ [n^{2/3}, n]` must be made explicit.  The proof needs:
   `HugeMargins n ρ ε γ κ ξ` (for Lemma 7.3), `1000ε ≤ 1`, the Kahn threshold
   `D₀(1/2, r) ≤ γ²D/20`, the Chernoff condition
   `k·2exp(-(γn/4)²/(2(r(n/t+γn/12)))) < 1` with `t = ⌈4/γ⌉`, and `D ≤ n`.
   **Threading design** (worked out, not yet implemented): since `D₀` is
   `∃`-quantified inside `KahnStatement`, the threshold must be stated with a
   *canonical* choice, `noncomputable def kahnD₀ (hK) (r) (hr) :=
   Classical.choose (hK (1/2) (by norm_num) r hr)`, so that the leftover lemma
   can take the hypothesis `20 * kahnD₀ hK r hr ≤ γ² * D`.  The assembly can
   then prove it by enlarging its own threshold `N₀` (it knows all of `s12_step1`'s
   constants and `hK`), and the hypothesis is threaded down
   `s12_step7 ← s12_steps67 / s12_core ← s12_chain ← the three mains ←
   eflStatement_of_deep` (each caller except the last already has, or can be
   given, the ambient `S12Margins`).
2. **The partition**: `exists_colouring_parts_ge t m` with `t := max 2 ⌈4/γ⌉₊`,
   `m := ⌈γ²D/10⌉₊` and `t*m ≤ k` (from `k ≥ γD/2`).  Then Kahn
   (`exists_list_colouring_in_part`) for each part, with the forbidden lists
   `C(e) ∩ P_j` where `C(e) = {c : e ∩ V(M_c) ≠ ∅}` (of size `≤ γ²D/100 ≤ D'/4`
   for `D' = γ²D/20`).
3. **The merging** (`exists_merged_colouring` with `W := n`, `τ := γn/4`,
   `C := r`, `t` as above): needs the class-size bound `Σ_{e ∈ class} |e| ≤ n`
   for a matching class, so a lemma "for a matching, the sum of edge sizes is
   `(famVert …).ncard ≤ n`" (not yet in the cone) and the conversion between
   the *weight* form produced by `exists_merged_colouring` and the *vertex*
   form needed below.
4. **The absorption** (`huge_edge_absorption` with `𝓗 := 𝓜.edgeSet`,
   `B := 0` and `𝓥 := {U, univ}`): the initial matchings are
   `N₀ c := toFam (M c ∪ ψ⁻¹(c))`; one checks `IsMatching`, pairwise
   disjointness, avoidance of `R`, and the smallness
   `(matchVert (N₀ c)).ncard ≤ γn/2 + γn/2` (this is the `AbsorbableBySmall`
   alternative), plus `hUdeg` from `U = V_+^{(1-ε)}(𝓗^(2))`.
   **SUBTLEty**: `toFam` *deletes the singleton edges*, so `matchVert (toFam G)`
   does not see vertices covered only by singletons; the final `N c` must
   therefore carry the singleton edges of `ψ⁻¹(c)` back (they cost one vertex
   each and are allowed to be shared by several classes, cf. `EdgeDisjointFam`).
   In the actual application (Step 7 of §12) `𝓗_rem ⊆ 𝓗.smallEdges r₁` with
   `𝓗` having no singleton edge, so this case does not arise; the proof should
   handle it generically nevertheless.
5. **Assembly** of the above into `leftover_colouring_lemma`, with the exact
   conclusion of `LeftoverStatement`, and then the replacement of the
   `LeftoverStatement` hypothesis by this theorem (Kahn is already a hypothesis
   of `eflStatement_of_deep`).

**STATEMENT REPAIR ALREADY DONE**: `LeftoverStatement` (Nibble.lean) now takes
the paper's linearity hypothesis `𝓗.IsLinear` as its first hypothesis (needed
for Kahn; the call site `s12_step7` supplies it from
`MultiHypergraph.isLinear_ofHypergraph hbig hlin`).  The faithfulness fix was
applied together with the `_bound`-rename of
`IsS12Colours.card_med_diff_huge_le_bound` described in the previous note.


## SESSION NOTE: `LeftoverProof.lean` -- STEPS 1--3 OF `lem:leftover` ARE DONE

`Submission/EFL/LeftoverProof.lean` (in the cone, sorry-free) now contains, on
top of the glue lemmas and the two colouring steps recorded in the previous
note:

* `toFamFull` (the family of *all* edges of `𝓗` with vertex set in `G`, keeping
  the singletons, unlike `toFam`), with `mem_toFamFull`, `matchVert_toFamFull`,
  `famOf_toFamFull`, `isMatching_toFamFull`,
  `MultiHypergraph.IsMatching.toFamFull_edgeSet`,
  `MultiHypergraph.isMatching_famOf_edgeSet` (the converse direction), and
  `edgeDisjointFam_toFamFull` (which needs the no-singleton hypotheses — without
  them `Disjoint (toFamFull N) (toFamFull N')` is *false*, since singleton edges
  may be shared).
* **`leftover_absorption`** — Step 3: from matchings `M i ∪ cls i` of small
  vertex set (`(famVert ·).ncard ≤ γn`) that avoid the absorber `R` and are
  pairwise edge-disjoint, Lemma 7.3 (`huge_edge_absorption`, applied to the
  hypergraph `𝓜.edgeSet` with `B := 0` and `𝓥 := {U, univ}`) produces matchings
  `N i = famOf (N' i)` with `M i ∪ cls i ⊆ N i`, `N i ∖ (M i ∪ cls i) ⊆ R`,
  pairwise `EdgeDisjointFam`, and the perfect/nearly-perfect coverage of `U`.
  The interface facts used: `matchVert (toFam G) = famVert G` (needs
  `∀ e ∈ G, 2 ≤ e.ncard`), `famOf (toFam G) = G` (`famOf_toFam_eq`), and
  `famVert (famOf M) = matchVert M` (`famVert_famOf`; NB the rewrite direction
  matters — the lemma rewrites `famVert (famOf ·)` **to** `matchVert ·`, so to
  use it on a hypothesis about `matchVert` one needs `rw [← famVert_famOf]`,
  and to turn a goal about `famVert` into one about `matchVert`,
  `rw [famVert_famOf]`).

**REFACTOR**: the conclusion of `LeftoverStatement` (Nibble.lean) is now the
named predicate **`LeftoverConcl 𝓗 𝓗rem R U S ε M N`**, and the statement reads
`∃ N, LeftoverConcl 𝓗 𝓗rem R U S ε M N`.  This lets a proof of the
(repaired, margin-carrying) lemma state its conclusion without duplicating it.

**REMAINING: Step 4 (the assembly) and Step 5 (wiring).**  The plan, with the
exact hypotheses the proof will need (all of them provable for `n` large from
the constant hierarchy; they belong in a `LeftoverMargins`-style bundle or in
an enlarged threshold at the assembly level):

* `hm : HugeMargins n ρ ε γ (1/2) ξ`, `4 ≤ n`, `(D:ℝ) ≤ n`;
* the Kahn data: `∃ D₀, 0 < D₀ ∧ (∀ D, D₀ ≤ D → ∀ 𝓖, 𝓖.IsLinear →
  Δ(𝓖) ≤ D → (∀ e ∈ 𝓖, edgeSize e ≤ r) → ∀ c, (3/2)D ≤ c → ∀ L, (∀ e, |L e| ≤
  D/4) → ∃ ψ, ∀ e, ψ e ∉ L e) ∧ 20 D₀ ≤ γ²D` (derivable from `KahnStatement`
  for `α = 1/2` with the canonical `D₀` obtained from
  `kahn_colorable hK (by norm_num) hr`);
* `t := max 2 ⌈4/γ⌉₊`, `m := ⌈γ²D/10⌉₊`: `t * m ≤ k` (from `γD/2 ≤ k`),
  `4 ≤ γ * t` (so that `n/t ≤ γn/4`);
* the Chernoff condition `k * 2 exp(-(γn/4)²/(2(r(n/t + γn/12)))) < 1`.

Then: split the colour set `Fin k` with
`Commons.Combinatorics.Partition.exists_colouring_parts_ge`; for each part `P j`
apply `exists_list_colouring_in_part` with the lists
`L e := {c ∈ P j | (e ∩ famVert (M c)).Nonempty}` (of size `≤ γ²D/100 ≤ D'/4`
for `D' = γ²D/20`, since `{i | e ∩ famVert (M i) ≠ ∅}` has size `≤ γ²D/100` by
L4 and `L e` is a subset of it); merge with `exists_merged_colouring`
(`W := n`, `τ := γn/4`, `C := r`); note that in the merged colouring two edges
with the same colour must have been sent to the *same* part (the parts are
disjoint and both contain the colour), which is what makes each merged class a
matching; then apply `leftover_absorption`.

Two further lemmas are needed on the way (neither is in the cone yet):
* for a matching family `N` of subsets of `Fin n`,
  `∑_{e ∈ N} e.ncard = (famVert N).ncard ≤ n` (Finset version:
  `Finset.card_biUnion` with `f e := e.toFinset` for a pairwise disjoint
  family);
* the class-size arithmetic turning `n/t + γn/4 ≤ γn/2` into
  `(famVert (cls c)).ncard ≤ γn/2`.

Finally, the repair of `LeftoverStatement` (already done: linearity, no
singletons in the `M i` and in `𝓗rem`) plus the new margin hypotheses must be
threaded: at the call site `s12_step7` the no-singleton facts are
`hMns`/`hremNs` (already proved there from `hbig` and
`large_nonhuge_of_buff_union_final`), and the margin facts have to travel down
from the assembly (where the threshold `N₀` can be enlarged).

-/


/-!
## SESSION NOTE: `lem:leftover` IS PROVED AND WIRED IN -- `LeftoverStatement` IS GONE

`timeout 3600 lake build Challenge Solution Submission` = **3341 jobs GREEN**;
the only `sorry` in the cone is the intended `theorem_1_1` (`Submission.lean`,
line ~1452).  No fixed file touched.

**The headline: `eflStatement_of_deep` now takes only FOUR deep inputs**

    theorem eflStatement_of_deep (hMR : MolloyReedStatement) (hK : KahnStatement)
        (hNib : NibbleStatement) (hGKO : GKOStatement) : eflStatement

The `LeftoverStatement` hypothesis has been **eliminated**: the paper's Lemma
`lem:leftover` is now *proved* from `KahnStatement` + Lemma 7.3
(`huge_edge_absorption`) and wired all the way down the §12 chain.

### 1. New module `Submission/EFL/LeftoverLemma.lean` (788 lines, sorry-free)

Contains everything that was in `LeftoverProof.lean` *and* `LeftoverFinal.lean`
(the two files are now one-line stubs `import Submission.EFL.LeftoverLemma`,
so the old module names still work), plus:

* `leftover_colouring_lemma` — **the formalised Lemma `lem:leftover`**: from
  `KahnStatement`, a linear multi-hypergraph `𝓜`, the data L1--L5 and the
  numerical hypotheses (Kahn's threshold `20·kahnD₀ ≤ γ²D`, the Chernoff
  condition, `HugeMargins n ρ ε γ (1/2) ξ`, `4 ≤ n`, `D ≤ n`), it produces
  `∃ N, LeftoverConcl 𝓜 𝓗rem R U S ε M N`.  The proof is the paper's:
  partition `Fin k` into `t = max 2 ⌈4/γ⌉` parts of size `≥ m = ⌈γ²D/10⌉`
  (`Commons.Combinatorics.Partition.exists_colouring_parts_ge`); per part apply
  Kahn's theorem with the forbidden lists `{c ∈ P j : e ∩ V(M_c) ≠ ∅}`
  (`exists_list_colouring_in_part`); merge the `t` colourings by a balanced
  random choice (`exists_merged_colouring`, from the commons
  `exists_colouring_bounded_load`); then extend each `M_c ∪ ψ⁻¹(c)` by the
  absorber (`leftover_absorption`, Lemma 7.3).

  The **key new mathematical step** is the identification of the colour class
  `cls c` of the *merged* colouring as a matching: two edges coloured `c` must
  have been sent to the same part (the parts are disjoint, and both contain
  `c`), hence the same `ψ_j` colours them, hence they are disjoint; and every
  edge of `cls c` is disjoint from `famVert (M c)` by the Kahn list-avoidance.

* the small counting lemmas used by it: `famVert_finset_eq_biUnion`,
  `ncard_famVert_finset_le` (always true, no disjointness needed),
  `sum_edgeSize_le_of_pairwise_disjoint` (a pairwise disjoint family of subsets
  of `Fin n` has total size `≤ n`), `ncard_setOf_eq_card_filter`.

### 2. New module `Submission/EFL/LeftoverMargins.lean` (470 lines, sorry-free)

Placed **below `S12Step7`** in the import order (imports only `DeepInputs`,
`HugeStep`, `S12Setup`, and the commons exp lemma) so that the §12 chain can
use it.  Contains

* `KahnListBody`, `kahnD₀`, `kahnD₀_pos`, `kahnD₀_body` (Kahn at `α = 1/2`),
  `kahnD₀'` (`= kahnD₀ hK (max r 2)`);
* `leftoverT γ = max 2 ⌈4/γ⌉`, `leftoverM γ D = ⌈γ²D/10⌉` and their arithmetic
  (`four_le_mul_leftoverT`, `div_leftoverT_le`, `div_leftoverT_add_le`);
* **`structure LeftoverMargins (n r₁ : ℕ) (γ ρ ρ_abs ε ξ : ℝ) : Prop`** — the
  numerical bundle: `hK : KahnStatement` (a *field*, so that the whole bundle
  is one hypothesis!) plus `hn4`, `hDn` (`Dparam n ρ ≤ n`), `hkanthr`,
  `hTm`, `hcher` (stated with `D = Dparam n ρ`, `k = D'param (Dparam n ρ) γ`)
  and `hm : HugeMargins n ρ_abs ε (10√γ) (1/2) ξ`.  Note `ρ` (which enters via
  `Dparam`) and `ρ_abs` (the absorber density) are *different* parameters —
  they coincide in Type A₁/B but are `σ/2` vs `σ/4` in Type A₂;
* **`exists_leftoverMargins`**: for a constant hierarchy
  `0 < γ ≤ 1/100`, `0 < ρ ≤ 1/4`, `0 < ρ_abs ≤ 1`, `1000ε ≤ 1`, `0 < ξ`,
  `10⁴√γ ≤ ρ_abs ε`, `4000ξ ≤ √γ ρ_abs`, all the fields hold for all large
  `n`.  Proved by `filter_upwards` on six `∀ᶠ`-statements; the Chernoff
  condition uses the (new, delegated) commons lemma
  `Commons.Analysis.Real.exists_mul_exp_neg_lt_one`.

### 3. THE CONSTANTS OF TYPE B HAD TO BE FIXED (`γ₂`: `10⁻²⁴ → 10⁻³⁰`)

This is a **genuine faithfulness fix hidden by the (unproved) `LeftoverStatement`**:
the buffer colour set has size `D' = ⌊10γ^{1/2} D⌋`, so the buffer's own
`γ`-parameter is `10√γ`, and Lemma 7.3 (`HugeMargins`) requires
`1000·(10√γ) ≤ ρ_abs ε`, i.e. `10⁴√γ ≤ ρ_abs ε`.  In the Type B branch
`ρ_abs = 10⁻⁵`, `ε = 10⁻⁴` give `ρ_abs ε = 10⁻⁹`, so one needs `γ₂ ≤ 10⁻²⁶`
(the old value `10⁻²⁴` only satisfied `1000·(3γ/2) ≤ ρ_abs ε`).  Changed in
`Submission/EFL/S12Step1Full.lean` (`s12_step1`'s invariant `γ₂ ≤ 10⁻³⁰`, and
the definition `γ₂ := 10⁻³⁰`), and correspondingly `s12_B_main`'s hypothesis
`hγ24 : γ ≤ 10⁻³⁰`; `s12_B_main` then weakens it to `≤ 10⁻²⁴` for the
existing consumers (`exists_S12BNum`).  Everything downstream of `γ₂`
(`δ, σ, γ₁, β, r₀, N₀`) is *derived* from it, so the whole hierarchy shrinks
consistently and every `∃ N`-threshold adapts automatically.

### 4. THE TWO "MARGINS FOR THE CONSTANTS" HELPERS

* `exists_leftoverMargins_A` (`Submission/EFL/S12ANum.lean`): for
  `ρ = σ/2`, `ρ_abs ∈ {σ/2, σ/4}`, `ε = σ³/10⁴²`, `γ ≤ σ¹⁰/10²⁵⁰`,
  `√γ ≤ σ⁵/10¹²⁵`, `10ξ ≤ γ/2`, gives
  `∃ N, ∀ n ≥ N, LeftoverMargins n r₁ γ (σ/2) ρ_abs (σ³/10⁴²) ξ`.
* `exists_leftoverMargins_B` (`Submission/EFL/S12BNum.lean`): for
  `ρ = ρ_abs = 10⁻⁵`, `ε = 10⁻⁴`, `γ ≤ 1/10³⁰` and
  `4000ξ ≤ (3γ/2)·10⁻⁵` (the `S12Margins` field `hmHuge.hξγρ`), gives the
  analogous statement.

### 5. THE WIRING (which files changed)

* `Submission/EFL/S12Step7.lean`: imports `LeftoverLemma`; the hypothesis
  `(hLeft : LeftoverStatement)` became
  `(hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ)`, and the application of the
  leftover lemma became `leftover_colouring_lemma hleft.hK (le_max_right r₁ 2)`
  with the margins discharged from `hleft` by rewriting `hS12.hCmain_card`,
  `hS12.hCbuff_card`.
* `s12_steps67` (`S12Assem.lean`), `s12_core` (`S12Core.lean`), `s12_chain`,
  `s12_main_A1` (`S12Final.lean`), `s12_chain_gen`, `s12_to_S12Out_gen`
  (`S12ChainGen.lean`), `s12_to_S12Out`, `s12_branch_A2` (`S12MainA2.lean`),
  `s12_branch_A1` (`S12MainA.lean`), `s12_branch_B` (`S12MainB.lean`): the
  hypothesis became `(hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ)` (or with
  the hard-coded constants of the branch, e.g.
  `LeftoverMargins n r₁ γ (1/10⁵) (1/10⁵) (1/10⁴) ξ` for Type B).
* The three mains `s12_A1_main`/`s12_A2_main`/`s12_B_main` now take
  `(hK : KahnStatement)` instead of `hLeft`, extract the *constant* facts from
  an `S12ANum`/`S12BNum` instance at `n = max N₁ 1` (because `hξsharp` and
  `hsqrtγ` are only available inside the `∀ n ≥ N`), call
  `exists_leftoverMargins_A`/`_B` to get a further threshold `N₄`, and pass
  `hN₄ n hn₄` to the branch.
* `eflStatement_of_deep` (`S12Assembly.lean`): `hLeft` dropped, `hK` passed.
* `Nibble.lean`: gained the glue lemmas `nonsing_eq_self`, `toFam_eq_self`,
  `famOf_toFam_eq` (moved from `S12Assem.lean`), `mem_toFam_iff`,
  `matchVert_toFam` (moved from `S12Step7.lean`) — necessary because the
  leftover lemma had to move *below* `S12Step7`.

### 6. NEW COMMONS LEMMA (proved by the requested fleet)

* `Commons.Analysis.Real.exists_mul_exp_neg_lt_one`
  (`Submission/Commons/Analysis/Real/exists_mul_exp_neg_lt_one.lean`):
  `0 ≤ a → 0 ≤ b → 0 < c → ∃ N, ∀ n ≥ N, (a·n + b)·exp(-(c·n)) < 1`.
  Proved via `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` and
  `eventually_lt_const`.

### 7. LEAN LESSONS (new)

(a) **`rw` rewrites gamma inside `√γ`.**  `rw [h]` with `h : √γ * √γ = γ` (or
    `γ = √γ*√γ`) also rewrites the `γ` *under the square root* in the
    occurrences of `√γ`, giving `√(√γ^2)`.  Work with `nlinarith`/`calc` and
    an explicit `hs : √γ * √γ = γ` instead of `rw`.
(b) **`linarith` cannot chain `zpow` numerals**: from
    `h1 : γ ≤ (10:ℝ)^(-30:ℤ)` and `h2 : (10:ℝ)^(-30:ℤ) ≤ 1/100` it does *not*
    prove `γ ≤ 1/100`.  State the bound as `γ ≤ 1/10^30` (a `div`-numeral) —
    then `linarith` chains it fine.  (Converting `10^(-30:ℤ) = 1/10^30` with
    `norm_num` in a separate `have` works.)
(c) `Finset.sum_image` in this Mathlib takes `Set.InjOn g ↑s` as a single
    argument and has the signature
    `∑ x ∈ s.image g, f x = ∑ x ∈ s, f (g x)` — note `f` is the *summand* and
    `g` the *map*; passing them the wrong way round gives a confusing
    "Subtype.ext has type ..." error.
(d) `neg_div` rewrites `-(a/b) → -a/b`; to go the other way use an explicit
    `have h1 : -a/b = -(a/b) := by rw [neg_div]` and `rw [h1]`.
(e) `obtain ⟨x, hx⟩ := h` where the goal is itself `∃ x, P x` *closes the
    goal* by `⟨x, hx⟩`, so a following `· exact ⟨x, hx⟩` errors with
    "No goals to be solved"; use `have hex : ∃ x, P x := ...` + `exact hex`.
(f) `structure ... : Prop` may carry a `Prop`-valued field (`hK` below) that
    later fields refer to by name — this is what makes `LeftoverMargins` a
    single hypothesis for the whole chain.
(g) When a lemma must be applied *below* a module that currently defines it,
    the fix is to move the lemma (and its dependencies) down: here
    `matchVert_toFam`, `toFam_eq_self`, `famOf_toFam_eq`, `nonsing_eq_self`,
    `mem_toFam_iff` moved into `Nibble.lean`, and `LeftoverProof`'s need for
    `S12Assem` disappeared.
(h) A file edited with `lake env lean F.lean` gets *type-checked* but its
    `.olean` is **not** updated, so importers still see the stale version; run
    `lake build <module>` before checking the importer.

### 8. REMAINING WORK (unchanged in kind, now one input shorter)

The four deep inputs `MolloyReedStatement`, `KahnStatement`, `GKOStatement`,
`NibbleStatement`; of these only `NibbleStatement` (`lem:nibble2`) is itself a
*theorem* of the paper (§§8--9) and hence a candidate for the same treatment:
it is proved from `SparseEGJStatement`/`EGJStatement` + `lem:embed`
(**not yet stated** in the cone; it needs an API for hypergraphs on a *larger*
vertex set, since it embeds an `N`-vertex hypergraph into an `r`-uniform linear
hypergraph on `≤ r(r-1)²D³N` vertices) + `lem:pseudorandom_matching`.

-/

/-!
## PLAN FOR THE NEXT SESSIONS (after `lem:leftover` was eliminated)

The cone is green (3341 jobs) with `theorem_1_1` the only `sorry`, and

    eflStatement_of_deep : MolloyReedStatement → KahnStatement →
                           NibbleStatement → GKOStatement → eflStatement.

### (A) FIRST: make `NibbleStatement` faithful (mirror of what was just done)

`NibbleStatement` (`Submission/EFL/Nibble.lean`) is, as written, **strictly
stronger than the paper's `lem:nibble2`** (the "Main colouring lemma",
`efl.tex:1737`) and hence *unprovable*: the paper's hypotheses are

    `0 < 1/n₀ ≪ 1/r, ξ, β ≪ γ ≪ ε, ρ ≪ 1`, `n ≥ n₀`, `D ∈ [n^{2/3}, n]`

together with C1--C4 (see the paper), whereas the cone's version has no
`n`-large and no `≪`-hypotheses at all.  Exactly the same phenomenon as with
`LeftoverStatement` (whose proof needed `HugeMargins`, Kahn's threshold and the
Chernoff condition).  The repair follows the `LeftoverMargins` recipe:

1. Define a `structure NibbleMargins (n r D β γ ε ρ ξ κ : ...) : Prop` (or with
   the parameters that the §12 chain actually has) bundling
   `(n : ℝ) ^ (2/3) ≤ D` (the paper's `D ∈ [n^{2/3}, n]`; in the application
   `D = Dparam n ρ ≈ n`), `1 ≤ n`, and the `≪`-statements
   `0 < 1/n ≪ 1/r, ξ, β ≪ γ ≪ ε, ρ` in the form of explicit constant
   inequalities (as `HugeMargins` does).
2. Add it as an extra hypothesis to `NibbleStatement` (whose *only* application
   site is `Submission/EFL/S12Step6.lean:462`, `hNibApp := hNib ...`).
3. Thread `(hnib : NibbleMargins ...)` through `s12_step6` and then through the
   same chain functions that carry `hNib` today (`s12_steps67`, `s12_core`,
   `s12_chain`, `s12_main_A1`, `s12_chain_gen`, `s12_to_S12Out_gen`,
   `s12_to_S12Out`, `s12_branch_A1/A2/B`, and the three mains) -- mechanically
   identical to the `hleft` threading, except that it is *not* discharged
   (the nibble remains a deep input).
4. The three mains *produce* `NibbleMargins` from the constants (pure
   arithmetic, as `exists_leftoverMargins_A/_B` does for the leftover).

This makes `eflStatement_of_deep` an honest conditional theorem: every input is
stated with all the hypotheses its proof actually uses.

### (B) THEN: the §8/§9 reduction of `lem:nibble2`

The paper proves `lem:nibble2` from
* `lem:embed` (`efl.tex:535`) -- **not yet stated** in the cone.  It says: for
  `0 < 1/N₀, 1/D₀, 1/C₀ ≪ 1/r ≤ 1/3` and an `N`-vertex linear multi-hypergraph
  `𝓗` with `Δ(𝓗) ≤ D` and `|e| ≤ r`, there is an `r`-uniform linear hypergraph
  `𝓗_unif` on a **larger** vertex set with
  (E1) `𝓗 ⊆ 𝓗_unif|_V` and `𝓗_unif|_V ∖ 𝓗` consists of singletons,
  (E2) `D - C ≤ d_{𝓗_unif}(v) ≤ D` for all `v`, and `d_{𝓗_unif}(v) = d_𝓗(v)`
       when `d_𝓗(v) ≥ D - C`,
  (E3) `v(𝓗_unif) ≤ r(r-1)² D³ N`.
  Its proof: add `r - |e|` new vertices to each `e ∈ 𝓗` (making it `r`-uniform
  and linear), then take `T = (r-1)²D²` vertex-disjoint copies and, for each
  vertex `v` of deficiency `d_{𝓗*}(v) < D - C`, glue a copy of an auxiliary
  linear `T`-vertex `r`-uniform hypergraph `𝓗_d` with all degrees in
  `[d - c_r, d]`.  **Caveat**: the paper obtains `𝓗_d` from *Steiner systems*
  ("by considering Steiner systems, one can easily construct..."), which is a
  deep existence theorem; either a probabilistic/greedy construction is built
  instead, or this becomes a further explicit input.
  This needs a whole API for hypergraphs on a *larger* vertex set.  Note that
  the cone's `Hypergraph` is polymorphic (`abbrev Hypergraph (V : Type*) :=
  Set (Set V)`), so `Hypergraph (Fin n ⊕ Fin m)` is available; what is missing
  is `verts`/`edgeSize`/`matchVert`/`famOf`/... for a general vertex type
  (they are all stated for `Fin n`), and the transport of the §12 objects along
  `Fin n → Fin M`.
* `lem:pseudorandom_matching` (`efl.tex:1620`) -- the "Nibble Lemma" proper:
  from C3-style degree regularity `d_{𝓗'}(w) = (1±β)D`, families
  `𝓕_V, 𝓕_E` of size `≤ n^{log n}`, and `D` matchings `M_i` of few vertices,
  produce pairwise edge-disjoint matchings `N_i ⊇ M_i` with `N_i ∖ M_i ⊆ 𝓗'`
  that are `(γ,κ)`-pseudorandom w.r.t. `𝓕_V` and with
  `|F ∖ ⋃ N_j| ≤ γ|F| + κ max(|F|,D)` for every `F ∈ 𝓕_E`.
  Its proof: `lem:embed` then an `(r+1)`-uniform auxiliary hypergraph, then
  `Corollary cor:sparse_egj` (`SparseEGJStatement`).
* the paper's §8 `EGJ` machinery (`EGJStatement`/`SparseEGJStatement` in
  `Submission/EFL/EGJ.lean`) -- deep inputs.
* `lem:nibble2` itself is proved from these by partitioning `𝓗'` into
  `K = ⌈κ⁻¹⌉` parts of maximum degree about `D/K` (Chernoff + union bound),
  applying `lem:pseudorandom_matching` to each part and alternating with the
  crossing/internal absorption lemmas (`crossing_absorption`,
  `internal_absorption`, both already in the cone), and re-glueing.

### (C) The remaining irreducible deep inputs

`MolloyReedStatement`, `KahnStatement`, `GKOStatement` (+ `AKSStatement` /
`EGJStatement` / `SparseEGJStatement` for the nibble) are theorems of the
literature whose formalisation is research-scale; they stay as `Prop`-valued
inputs.  Everything else in §§1--12 plus `lem:leftover` is machine-checked.
-/
/-!
## SESSION NOTE: `NibbleStatement` IS NOW FAITHFUL (the margin bundle `NibbleMargins`)

Cone green: `timeout 3600 lake build Challenge Solution Submission` = **3342 jobs**,
the only `sorry` in the cone is `theorem_1_1` (`Submission.lean:1454`).

### 1. The gap

`NibbleStatement` (the paper's `lem:nibble2`, `efl.tex:1737`) was stated with
*no* asymptotic hypotheses at all:

    ∀ {n} (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n)) … (C1) … (C4) → concl

but the paper's hypotheses are

    0 < 1/n₀ ≪ 1/r, ξ, β ≪ γ ≪ ε, ρ ≪ 1,   n ≥ n₀,   D ∈ [n^{2/3}, n].

So the cone's version was strictly stronger than the paper's lemma (exactly the
same phenomenon as `LeftoverStatement` had, cf. the note on `lem:leftover`).
The *proof* of `lem:nibble2` needs, concretely:

* `D ≥ n^{2/3}` for the Chernoff bound of the partition step (`efl.tex:1760`),
* a `κ` with `1/r, ξ, β ≪ κ ≪ γ` and `K := ⌈κ^{-1}⌉` (`efl.tex:1760`),
* `β^{1/2} ≪ γ` — *not* merely `β ≪ γ`: the pseudorandom-matching lemma is
  applied on each part with `β^{1/2}` and `γ/4` (`efl.tex:1793`), and the
  transfer `|V(M_c)| ≤ βD ≤ β^{1/2} n_i` needs `β^{1/2} ≤ n_i/D ≈ κ/2`,
  i.e. `β ≲ γ²`,
* `3β ≤ γ/2` (condition `(d)_i`, `efl.tex:1811`).

### 2. The repair

* **NEW structure `NibbleMargins (n : ℕ) (D : ℝ) (r : ℕ) (β γ ε ρ ξ : ℝ) : Prop`**
  in `Submission/EFL/Nibble.lean`, with the fields
  `hn : 8 ≤ n`, `hr : 2 ≤ r`, `0 < β,γ,ε,ρ,ξ`, `hρ1 : ρ ≤ 1`,
  `hDlow : Real.rpow n (2/3) ≤ D`, `hDhigh : D ≤ n`,
  `hnr : 4r ≤ n`, `hnξ : 1 ≤ ξn`, `hnβ : 1 ≤ βn`, `hrγ : 4 ≤ γr`,
  `hξγ : 4ξ ≤ γ`, `hβγ : 16β ≤ γ²`, `hγε : 4γ ≤ ε`, `hγρ : 4γ ≤ ρ`.
  Each field is a consequence of the paper's hypotheses (take the constants
  sufficiently separated, and `n` large) and each is used in the proof.

* `NibbleStatement` now has `NibbleMargins n (D : ℝ) r β γ ε ρ ξ` as its
  *first* hypothesis (after `M`).

* **`s12_step1` had to be strengthened.**  The paper's chain is
  `… ≪ 1/r₁ ≪ β ≪ κ ≪ γ₁ ≪ …` (`efl.tex:2298`), but the cone's `s12_step1`
  only recorded `β ≤ γ₁` — from which `β ≤ γ²` is *not* derivable (β ≤ γ and
  γ ≤ 10⁻²⁴ allow β = γ = 10⁻²⁴, and then β² = 10⁻⁴⁸ ≪ β).  The
  construction in the proof of `s12_step1` already sets
  `β := min β₀ (γ₁/2)`, so it was strengthened to

      set β : ℝ := min β₀ (min (γ₁ / 2) (γ₁ ^ 2 / 16))
      … (0 < β ∧ β ≤ γ₁ ∧ β ≤ γ₁ ^ 2 / 16) ∧ …

  (`Submission/EFL/S12Step1Full.lean`); `Hβ` only needs `β ≤ β₀`, so the
  smaller value is admissible, and everything downstream (`32 ≤ βr₁`,
  `r₁ < β(r₀-1)`, `IsTypeA`/`IsTypeB`) adapts because `r₁`, `r₀` are chosen
  *after* β.

* **`S12Margins` carries the bundle.**  `S12Margins` (`S12Assem.lean:89`) gained
  the field

      hnib : NibbleMargins n ((Dparam n ρ : ℕ) : ℝ) r₁ (2 * β) (2 * γ) ε ρ_abs ξ

  and `S12Margins_of`/`exists_S12Margins` (`S12Params.lean`) build it.  Because
  `S12Margins` is already threaded through `s12_core`, `s12_chain`,
  `s12_steps67`, `s12_chain_gen`, `s12_to_S12Out*` and the three branches, the
  bundle reaches the *single* application site `s12_step6` **without any
  signature change to the chain functions**: only `s12_step6` gained one
  argument (`(hnib : NibbleMargins n (Dparam n ρ : ℝ) r₁ (2β) (2γ) ε ρ_abs ξ)`,
  converted to `(Cmain.card : ℝ)` via `hS12.hCmain_card` inside), and the two
  call sites `s12_core`/`s12_steps67` pass `hm.hnib`.

* **Two further constants had to be strengthened** so that `S12Margins_of` can
  build the bundle at the Step-6 instantiation `β_n = 2β`, `γ_n = 2γ`:
  * a new hypothesis `hβsq : 8 * β ≤ γ ^ 2` (needed for `16·2β ≤ (2γ)²`);
  * the old hypothesis `h3γ : 3 * γ ≤ ε` was replaced by
    `h8γε : 8 * γ ≤ ε` (needed for `4·2γ ≤ ε`), with `3γ ≤ ε` derived
    internally for `floor_mul_sub_one_add_le`.
  Both are supplied by the concrete branches: `exists_S12ANum` /
  `exists_S12BNum` now take `β ≤ γ²/16` (`8β ≤ γ²`) and prove `8γ ≤ ε`
  (`ε = σ³/10⁴²` resp. `10⁻⁴`).  The three mains `s12_A1_main`, `s12_A2_main`,
  `s12_B_main` and `eflStatement_of_deep`/`S12Assembly` thread the one extra
  constant `hβsq` (Type B derives `8β ≤ γ₂²` from `β ≤ γ₁²/16` and
  `γ₁ ≤ σ ≤ δ ≤ γ₂`).

* `LeftoverStatement`'s docstring already recorded the analogous repair; the
  same is now true of the nibble: `eflStatement_of_deep` consumes no
  `forgetful` version of `lem:nibble2`.

### 3. The two remaining C1/C3 gaps -- CLOSED

Two further hypotheses of the paper were also missing and have now been added,
so that the cone's statement has every hypothesis of the paper's lemma:

* **C1** now begins with `S ⊆ U`;
* **C3** now contains `(∀ e ∈ 𝓗'.edges, e ∉ R)` (the paper's `𝓗' ⊆ 𝓗 ∖ R`;
  the missing `Disjoint 𝓗'.edgeSet R` is used in N2).

Evidence at the call site: `s12_step6` gained the two hypotheses
`(hS₂U : S₂ ⊆ U)` and `(hR₂sub : R₂ ⊆ R_res)`, and proves
`∀ e ∈ 𝓗star.edges, e ∉ R₂` from
`𝓗star.edges = 𝓗'.edges ∖ 𝓕` and `𝓗'.edges = 𝓗.smallEdges r₁ ∖ R_res`
(`regularising_lemma`).  The two call sites `s12_core` and `s12_steps67`
produce those hypotheses (their previously-late `hR₂sub` proofs were moved
*before* the Step-6 call), using
`hstep5.hR₂_eq`/`hstep4.hR₁_eq`/`hRabs_sub` and `hstep5.hS₂_sub`/`hS₁subU`.

With this, `NibbleStatement` is exactly `lem:nibble2` of the paper: same
hypotheses (C1--C4 plus the `≪`-hierarchy of `NibbleMargins`), same
conclusion (N1--N3 plus the singleton bookkeeping NB1 the cone needs because
its `𝓗` is a *multi*-hypergraph).

### 4. Lean lessons (new)

(a) `linarith only [h]` does **not** expand `^`-atoms: use `nlinarith` for goals
    containing `γ ^ 2` (e.g. `8β ≤ γ²` from `β ≤ γ²/16`).
(b) `Le.mul_le_mul_iff_one_le_right` is not the name one wants for
    `1 ≤ ξ * n ↔ 1/ξ ≤ n`; proving it by hand
    (`ξ * (1/ξ) = 1` + `mul_le_mul_of_nonneg_left`) is fastest.
(c) When *strengthening* a numeric hypothesis of a low-level lemma
    (`3γ ≤ ε` → `8γ ≤ ε`), keep the weak form as an internal `have` so that the
    commons lemmas (`floor_mul_sub_one_add_le`) that want the weak form are
    unaffected.
(d) A new *field* of an already-threaded `Prop`-structure is a very cheap way to
    thread new numeric data: `S12Margins.hnib` propagated the whole
    `NibbleMargins` bundle to `s12_step6` at the cost of two call-site edits.

-/
/-!
## SESSION NOTE (cont.): `theorem_1_1` NOW *TRAVERSES* THE WHOLE ROAD

`Submission.lean`'s `theorem_1_1` is no longer a bare `sorry`.  It is now

    have hMR : MolloyReedStatement := by sorry
    have hK  : KahnStatement      := by sorry
    have hNib : NibbleStatement   := by sorry
    have hGKO : GKOStatement      := by sorry
    exact eflStatement_of_deep hMR hK hNib hGKO

so the four deep inputs are the *only* gaps, and the entire machine-checked
development (§§1--12, the reordering lemma, Theorem 1.2, Lemma 11.3, Claim
12.1, the three branches of §12 and `lem:leftover`) is actually applied to the
statement of the challenge theorem.  Any future statement/definition drift
(e.g. `eflStatement` no longer being definitionally `theorem_1_1`'s type, or a
broken hypothesis in the assembly) now becomes a compile error instead of
being hidden behind one `sorry`.  `lake build Challenge Solution Submission`
is green (3342 jobs).

## AUDIT: ALL FIVE DEEP INPUTS ARE NOW FAITHFUL

With the nibble repaired, every deep input in the cone records the
hypotheses its proof actually uses:

| input | file | asymptotic hypotheses |
|---|---|---|
| `MolloyReedStatement` | `LocallySparse.lean` | `∃ Δ₀`, `Δ₀ ζ ≤ C/ζ^m`, `Δ₀ ζ ≤ Δ` ✓ |
| `AKSStatement` | `LocallySparse.lean` | `ζ ≤ ζ₀`, `Δ₀ ≤ Δ` ✓ |
| `KahnStatement` | `DeepInputs.lean` | `∃ D₀, D₀ ≤ D` ✓ |
| `GKOStatement` | `OptCol.lean` | `∃ N₀, N₀ ≤ n`, `0 < ν,ε`, `ε < p < 1` ✓ |
| `EGJStatement` | `EGJ.lean` | `∃ Δ₀, Δ₀ ≤ Δ`, `e(𝓗),|𝓕| ≤ exp(Δ^{ε²})` ✓ |
| `SparseEGJStatement` | `EGJ.lean` | `∃ n₀, n ≥ n₀`, `D ≥ n^{1/100}`, `κ,γ ∈ (0,1]` ✓ |
| `NibbleStatement` | `Nibble.lean` | `NibbleMargins` ✓ (this session) |

(`LeftoverStatement` remains in the file but is *unused* -- `lem:leftover` is
proved as `leftover_colouring_lemma`.)

## NEW COMMONS LEMMAS (this session, by the fleet)

* `Commons.Combinatorics.Hypergraph.sum_choose_two_le_choose_two`
  (module `Submission.Commons.Combinatorics.Hypergraph.sum_choose_two_le_choose_two`):
  `𝓕.sum (fun F => F.card.choose 2) ≤ n.choose 2` for a linear family
  `𝓕 : Finset (Finset (Fin n))` -- the pair-counting bound used to bound the
  number of edges of a linear hypergraph.
* `Commons.Analysis.Real.rpow_two_thirds_le_half`:
  `8 ≤ n → Real.rpow n (2/3) ≤ n/2`.
* `Commons.Combinatorics.Hypergraph.exists_linear_regular_uniform`
  (requested; see the plan below): for `r ≥ 2`, `p` prime and `d ≤ p` there is
  an `r`-uniform linear family on `Fin (r*p)` in which every vertex has degree
  exactly `d`.  This is the auxiliary design `𝓗_d` of `lem:embed`; the proof
  is the cyclic construction on `Fin r × ZMod p`,
  `E(a,x) = {(i, x + a i) : i < r}` for `a ∈ B` (any `d`-subset of `ZMod p`)
  and `x ∈ ZMod p` -- linearity is exactly the invertibility of the nonzero
  differences in the field `ZMod p`.

## PLAN FOR THE §8/§9 REDUCTION (updated)

The remaining two big pieces, in dependency order:

1. **`EmbedStatement`** (`lem:embed`, `efl.tex:535`) -- *not yet stated*.
   Required interface (this is the design worked out this session):
   given `2 ≤ r`, `N, D, C` with the `≪`-hierarchy and a linear
   `𝓗 : MultiHypergraph N` with `Δ ≤ D` and `|e| ≤ r`, produce
   `M : ℕ`, `hMn : N ≤ M`, `ι := Fin.castLE hMn`, an `r`-uniform linear
   `𝓗u : Hypergraph (Fin M)` and `S := Set.range ι`, such that
   * (E1) for every edge of `𝓗` (proper edge, resp. every *copy* of a
     singleton `{v}`, counted `𝓗.singles v` times) there is a **distinct**
     `e* ∈ 𝓗u` with `e* ∩ S = ι '' e`, and every `e* ∈ 𝓗u` with
     `e* ∩ S ≠ ∅` arises this way (this is the `ψ`-bijection; note that
     multi-hypergraph multiplicities make this an injection from the
     *multiset* of edges of `𝓗`, which is exactly what the proof of
     `lem:pseudorandom_matching` uses);
   * (E2) `(1-β)D ≤ d_{𝓗u}(w) ≤ (1+β)D` for all `w : Fin M`, and
     `d_{𝓗u}(ι v) = 𝓗.deg v` whenever `𝓗.deg v ≥ D - C`;
   * (E3) `M ≤ r * (r-1)^2 * D^3 * N`.
   Proof: `𝓗*` = `𝓗` with `r - |e|` fresh vertices added to every edge;
   `T := r * p` with `p` prime `≥ D` (Bertrand); `T` vertex-disjoint copies of
   `𝓗*`; on the `T` clones of each `v` glue a copy of the `d`-regular design
   of `exists_linear_regular_uniform` with `d := D - d_{𝓗*}(v)`.
   The freshness bookkeeping (`Fin (N + r*|E|) ↪ Fin M` etc.) is the work.

2. **`PseudorandomMatchingStatement`** (`lem:pseudorandom_matching`,
   `efl.tex:1620`) -- *not yet stated*.  Its proof from `EmbedStatement` +
   `SparseEGJStatement` is **entirely deterministic** (the paper's proof,
   `efl.tex:1660--1735`): build the `(r+1)`-uniform incidence hypergraph
   `𝓗_aux` with vertex set `V(𝓗_unif) ⊔ ⋃_{i<D} V_i`, where
   `V_i := V_i^* ∖ φ(i, V(M_i))`, prove
   `d_{𝓗_aux} = (1 ± 2β)D` on `V(𝓗_aux)`, note
   `n ≤ n' := |V(𝓗_aux)| ≤ n^7` and `D ≥ (n')^{1/14}`, apply
   `SparseEGJStatement` to `𝓗_aux` with `κ := 2β`, `γ`, the family
   `𝓕^aux := ⋃_i {φ(i,A) ∖ φ(i,V(M_i)) : A ∈ 𝓕_V} ∪ {ψ⁻¹(F) : F ∈ 𝓕_E}`,
   and set `N_i := {ψ(e*) : e* = {v_1..v_r} ∈ E_meet, {e*, v_1^i..v_r^i} ∈ N*} ∪ M_i`.
   This is a large but purely combinatorial formalisation -- the natural next
   target.

3. **`lem:nibble2`** (`NibbleStatement`) from `PseudorandomMatchingStatement`:
   the paper's proof additionally needs the *probabilistic* partition of `𝓗'`
   into `K = ⌈κ^{-1}⌉` parts with degree `(1 ± 2β)D/K` (Chernoff + union bound
   using `D ≥ n^{2/3}`), then the alternation with `crossing_absorption` /
   `internal_absorption` (both already in the cone).

4. The irreducible research-scale inputs: `MolloyReedStatement`,
   `KahnStatement`, `GKOStatement`, `EGJStatement`/`SparseEGJStatement`.

## SESSION NOTE (cont. 2): `lem:embed` -- STATEMENT, UNIFORMISATION STEP, AND A SUBTLETY IN THE PAPER

Cone green: `timeout 10800 lake build Challenge Solution Submission` = **3342
jobs**; the only `sorry`s are the four deep inputs inside `theorem_1_1`.

### 1. `Submission/EFL/Embed.lean` -- `EmbedStatement` (NEW)

`EmbedStatement` records the case of `lem:embed` that is actually consumed by
the proof of `lem:pseudorandom_matching` (see §3 below), in the cone's
`MultiHypergraph` language:

    ∀ r ≥ 3, ∃ C₀ ≫ r, ∀ N, C ≥ C₀, D > 0, ∀ 𝓗 : MultiHypergraph N,
      𝓗.IsLinear → (∀ e ∈ 𝓗.edges, edgeSize e ≤ r) →
      (∀ v, 𝓗.deg v ≤ D) → (∀ v, 0 < 𝓗.deg v → D - C ≤ 𝓗.deg v) →
      ∃ M, ι : Fin N ↪ Fin M, 𝓖 : Hypergraph (Fin M),
        κ : ({e // e ∈ 𝓗.edges} ⊕ {p : Fin N × ℕ // p.2 < 𝓗.singles p.1}) ≃
            {e // e ∈ 𝓖 ∧ (e ∩ ι '' {v | 0 < 𝓗.deg v}).Nonempty},
        (∀ e ∈ 𝓖, edgeSize e = r) ∧ 𝓖.IsLinear ∧
        (M : ℝ) ≤ r(r-1)²D³N ∧
        (E1) ∀ e ∈ 𝓗.edges, κ (inl e) ∩ ι '' V = ι '' e ∧
             ∀ v k < 𝓗.singles v, κ (inr (v,k)) ∩ ι '' V = {ι v} ∧
        (E2) ∀ w, D - C ≤ hdeg 𝓖 w ≤ D ∧
             ∀ v, 0 < 𝓗.deg v → hdeg 𝓖 (ι v) = 𝓗.deg v.

`κ` is the paper's `ψ : e* ↦ e* ∩ V(𝓗)`.

### 2. `Submission/EFL/EmbedProof.lean` -- the uniformisation step (PROVED)

    theorem exists_uniform_extension {𝓗 : Hypergraph (Fin n)} {r : ℕ} (hr : 2 ≤ r)
        (hlin : 𝓗.IsLinear) (h2 : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
        (hsize : ∀ e ∈ 𝓗, edgeSize e ≤ r) :
        ∃ M ι 𝓖, (∀ e ∈ 𝓖, edgeSize e = r) ∧ 𝓖.IsLinear ∧
          (∀ e ∈ 𝓗, ∃! e' ∈ 𝓖, e' ∩ Set.range ι = ι '' e) ∧
          (∀ e' ∈ 𝓖, (e' ∩ Set.range ι).Nonempty) ∧
          (∀ v : Fin n, hdeg 𝓖 (ι v) = MultiHypergraph.hdeg 𝓗 v) ∧
          (M : ℝ) ≤ n + r * 𝓗.ncard

with `M := n + r * #E(𝓗)`, `ι := Fin.castLEEmb`, and the block of `r` fresh
vertices `[n + r*i, n + r*(i+1))` reserved for the `i`-th edge of `𝓗`
(`i` from `Finset.equivFin 𝓗.toFinset`).  This is step 1 of the construction of
`lem:embed`, and it is the reusable "make a linear hypergraph `r`-uniform
without changing the old edges or their degrees" lemma.

Helper: `mem_range_castLEEmb : w ∈ Set.range (Fin.castLEEmb h) ↔ w.val < n`.

Refactor: `edgeSize_eq_ncard` (previously in `ColourClassSplitting.lean`) was
moved **down** into `Counting.lean`, so it is available at the bottom of the
cone.  (This forces a large but harmless rebuild.)

### 3. THE SUBTLETY (important for the next session)

The paper's E1 says "`𝓗_unif|_V ∖ 𝓗` only contains singleton edges", and the
proof of `lem:pseudorandom_matching` then asserts *a bijection*
`ψ : E_meet → 𝓗'`, `e* ↦ e* ∩ V(𝓗')`, where
`E_meet = {e ∈ 𝓗_unif : e ∩ V(𝓗') ≠ ∅}` (`efl.tex:1670`).

Literally, this is **not** a bijection in general: an auxiliary design `𝓗_d`
glued on the `T` clones of a vertex `v ∈ V(𝓗')` of *small* degree
(`d_𝓗(v) < D - C`) produces `d` edges that all meet `V(𝓗')` in `{v}`; they
therefore belong to `E_meet` but are not accounted for by `𝓗'`'s edge multiset
(and `ψ` maps all of them to the *same* singleton `{v}`, which need not even be
an edge of `𝓗'`).

The resolution -- and the reason the paper is still correct -- is that in the
application `lem:embed` is invoked on `𝓗'` with `D ↦ (1+β)D` and `C ↦ 2βD`,
while `d_{𝓗'}(w) = (1 ± β)D ≥ (1-β)D = D - C` holds at every `w ∈ V(𝓗')`; so
**no design is glued at any non-isolated old vertex**, and `E_meet` is exactly
the set of copy-`0` edges: `ψ` is a bijection onto `𝓗'`'s edges counted with
multiplicity, as claimed.

This is why `EmbedStatement` above carries the extra hypothesis
`∀ v, 0 < 𝓗.deg v → D - C ≤ 𝓗.deg v` (making it *weaker* than the paper's
lemma, hence implied by it), and why the "meet" set is `ι '' V(𝓗)` rather than
`Set.range ι`:  with this reading
* design edges at **isolated** old vertices and at the **fresh** vertices do not
  meet `ι '' V(𝓗)` (an isolated vertex is not in `V(𝓗)`, and fresh vertices are
  not in the range of `ι`);
* every `𝓗`-edge (with its multiplicity, including the singletons) is supported
  on `V(𝓗)`;
* `E_meet ↔ 𝓗`-edges-with-multiplicity is exactly what the proof of
  `lem:pseudorandom_matching` uses.

**Do not** weaken `EmbedStatement` back to "every degree is in `[D-C,D]`", and
**do not** state the general `lem:embed` with the `κ`-bijection unless the
`E_meet`-extras are handled explicitly.

### 4. What remains of `lem:embed`'s proof

Given `exists_uniform_extension` (step 1), the rest is:
1. the multi-hypergraph uniformisation (proper edges as above, and each of the
   `𝓗.singles v` singleton *copies* gets its own `r`-edge with `r-1` fresh
   vertices);
2. `T := r * p` vertex-disjoint copies on `Fin T × Fin M₁`, `p` a prime with
   `D ≤ p ≤ 2D` (Bertrand: `Nat.exists_prime_lt_and_le_two_mul`), so that
   `T ≤ 2rD` and (E3) follows from `∑_v 𝓗.deg v = ∑_e |e| ≤ D·N`;
3. on the clones of every *fresh* vertex (`d = 1`) and of every *isolated old*
   vertex (`d = 0`), glue a copy of the `D-d`-regular design of
   `exists_linear_regular_uniform` (with `r = r`, `p` as above, `d' := D - d`);
4. verify E1/E2 (each clone of `v` gets degree `d_{𝓗*}(v) + (D - 1)` etc.).

-/

/-! ## SESSION (2026-09-28/29) — THE **CONE SWITCH** AND THE KAHN/NIBBLE WIRING

`lake build Submission` is green with **exactly one** `sorry` (the `GKO` input inside
`Submission.theorem_1_1`), and `lake build Solution` is green.  `MolloyReedStatement`,
`KahnStatement` and `NibbleStatementFixed` are no longer inputs: they are supplied by
`Work.Deep.Sparse.molloyReedStatement`, `Work.Deep.Kahn.kahnStatement` and
`Work.Deep.Nibble.nibbleStatementFixed` in `Submission.lean`.

### 1. The GKO input became the paper's faithful form

`Submission/EFL/OptCol.lean`: `GKOStatement` is now the **faithful existential-threshold** form
of Theorem 10.8 — its body is written out *verbatim* as
`Work.Deep.GKO.GKOStatementFixed`'s, so the two `Prop`s are definitionally equal (machine check:
`Work.ConeSwitch.gkoStatement_eq_fixed := rfl`); the definition cannot be an `abbrev` of the
chapter's, because `Submission/Work/Deep/GKO/Defs.lean` imports `Submission.EFL.OptCol`.  The
old linear-hierarchy form (and its SESSION-4 warning block) is retained as
`GKOStatementLinear`, and the *conditional* corollaries
`optcol_corollary_core/_even/_odd` are stated for it (they are no longer on the critical path).

`Submission/EFL/OptColFaithful.lean` (new): the **faithful** Corollary 10.13, named
`ErdosFaberLovaszConjecture.optcol_corollary`, is `Work.S12Faithful.optcol_corollary_faithful`
applied to `GKOStatement`.  It cannot live in `OptColOdd.lean` as the original plan had it:
`Submission/Work/Deep/GKO/corollary_10_13_odd_from_fixed.lean` imports `OptColOdd` (for the
odd-case reduction), so `OptColOdd` is *upstream* of the `GKO` chapter and an import of
`Work.S12Faithful.Cone` there would be an import cycle (this was observed as a `lake` "build
cycle detected" error).

### 2. §12 was re-architected around the faithful input

`Submission/EFL/S12Assembly.lean`: `eflStatement_of_deep` is now a one-line reference to
`Work.ConeSwitch.eflStatement_of_deep_faithful` (`Submission/Work/ConeSwitch/Assembly.lean`),
which

* walks the constant hierarchy of Theorem 6.7 by hand (`γ₂ := 10⁻³⁰`, `δ`, `σ`, `γ`, `β`, `r₁`,
  `r₀`), each below the corresponding threshold of `largeEdgeThmStatement_of_deep`;
* chooses the Type-A₂ density `ρ := σ/2` **first**, applies the faithful Corollary 10.13 at the
  density `ρ/4` of the final graph (giving `η₀, ε₀`) and only then produces
  `ε, ζ, η, ηr` (`Work.ConeSwitch.exists_A2_params`) and `ξ`, `N`
  (`Work.S12Faithful.exists_S12A2Data_of_small`) *below* those thresholds;
* takes the case split at that **free** `(ρ, ε)`: `IsFull 𝓗 ρ ε` gives the Type-A₂ branch
  (`Work.S12Faithful.s12_branch_A2_faithful`), otherwise the Type-A₁ branch
  (`Work.ConeSwitch.s12_branch_A1_faithful`, new — its reservoir is `IsReservoirTypeA1` and the
  finishing is Vizing's theorem).  Both branches are parametric in `(ρ, ε)` as in the paper.

The pinned colouring input `s12_A2_main` was **deleted** from `Submission/EFL/S12A2Main.lean`
(the module is now a documented stub): the pinned architecture would need one `σ` with
`σ/2 = ρ ≥ 4p*` and simultaneously `σ³/10⁴² ≤ ε₀(p*)`, `22σ³/10⁴² ≤ η₀(p*)` — a fixed-point
condition in the unknown threshold functions, unsolvable in general.  The chain
`s12_finish_A2_gen`/`s12_lowerRegular_final_gen`/`s12_to_S12Out` (`S12MainA2.lean:38--153`) is
reused **verbatim** (only the `hNib` parameter type of the two callers changed).

### 3. The Nibble input: the proved form is asymptotic, the cone threads a threshold

The Nibble chapter proves `Work.Deep.Nibble.nibbleStatementFixed`, whose shape is the paper's
`∀ (constants, with `MarginsConst`), ∃ N₀, ∀ n ≥ N₀, ∀ data, …`.  The cone cannot restate that
pointwise (the witness `N₀` is opaque, and the margins' `hnbig` does not dominate it), so
`Submission/EFL/NibbleFixed.lean` defines `NibbleStatementFixed` in exactly that asymptotic shape
plus `NibblePointwise r β γ ε ρ ξ n` (the same statement above a fixed `n`),
`nibbleThr r β γ ε ρ ξ` (the chosen threshold, `Classical.choose` of the asymptotic witness),
`nibbleAbove_nibbleThr` and `marginsConst_of_bundle`.  The eight cone files on the §12 path
(`S12Assem`, `S12Assembly`, `S12ChainGen`, `S12Core`, `S12Final`, `S12MainA`, `S12MainA2`,
`S12MainB`, `S12Step6`) carry `NibblePointwise` instead of a bare `NibbleStatementFixed` and each
branch main returns `max … (nibbleThr …)` as its threshold, deriving the pointwise hypothesis
from its own `NibbleMarginsStrong` bundle.  The seeded (false) `NibbleStatement` is kept in
`Submission/EFL/Nibble.lean` only because the chapter refutes it
(`Work.Deep.Nibble.not_nibbleStatement`).

### 4. Import hygiene (the `Hypergraph`-ambiguity trap)

`import Mathlib` anywhere in the cone's closure makes the root `Hypergraph` structure of
`Mathlib.Combinatorics.Hypergraph.Basic` ambiguous with `ErdosFaberLovaszConjecture.Hypergraph`,
and both `Submission.lean` and the fixed `Solution.lean` stop compiling.  `Submission/Work/`
gained `ConeSwitch/MathlibNoHG.lean`: every Mathlib module **except** `Mathlib.Combinatorics.
Hypergraph.Basic` and the umbrella `Mathlib` (that module is imported by nothing else in
Mathlib, so this is safe).  **168** `Work/Deep/{Kahn,Nibble,Prob,Conc,Reed}` modules that had
`import Mathlib` were rewritten to import it instead (their closures rebuild), and the whole
`Submission`/`ChallengeDeps` closure (8829 modules) now contains no module importing `Mathlib`.
A new `Work` module that is imported by the cone must use narrow Mathlib imports.
-/
