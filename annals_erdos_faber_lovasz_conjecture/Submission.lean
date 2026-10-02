import ChallengeDeps
import Submission.Helpers
import Submission.EFL.Basic
import Submission.EFL.LineGraph
import Submission.EFL.Matching
import Submission.EFL.Counting
import Submission.EFL.NeighbourSum
import Submission.EFL.OrderConcat
import Submission.EFL.SubfamilyConcat
import Submission.EFL.ColourCombine
import Submission.EFL.DeepInputs
import Submission.EFL.StabilityLoop
import Submission.EFL.ClassicalBounds
import Submission.EFL.LocallySparse
import Submission.EFL.Reordering
import Submission.EFL.EdgeSize
import Submission.EFL.LargeEdge
import Submission.EFL.LargeEdgeSetup
import Submission.EFL.MedEdges
import Submission.EFL.LargeEdgeCase1
import Submission.EFL.ReorderingSplit
import Submission.EFL.Fig3Blocks
import Submission.EFL.Fig3Case1
import Submission.EFL.ColourUnion
import Submission.EFL.ColourCombine2
import Submission.EFL.LargeEdgeBlocks
import Submission.EFL.LargeEdgeCase2
import Submission.EFL.WeakStability
import Submission.EFL.WeakStabilityMain
import Submission.EFL.FewLargeColourClasses
import Submission.EFL.ColourClassCounting
import Submission.EFL.ColourClassSplitting
import Submission.EFL.ColourClassSplitHonest
import Submission.EFL.AlphaBoundedColouring
import Submission.EFL.GreedyListColouring
import Submission.EFL.Reformulation
import Submission.EFL.BigEdges
import Submission.Commons.Combinatorics.SimpleGraph.vizing
import Submission.Commons.Combinatorics.SimpleGraph.vizing_two_max
import Submission.EFL.Nearfull.LinearNearfullColouring
import Submission.EFL.LargeEdgeCases
import Submission.EFL.LargeEdgeCase22
import Submission.EFL.LargeEdgeCase22Main
import Submission.EFL.Case21
import Submission.EFL.Case21Margins
import Submission.EFL.LargeEdgeHierarchy
import Submission.EFL.LargeEdgeThm
import Submission.EFL.Reservoir
import Submission.EFL.ReservoirExistence
import Submission.EFL.GFactor
import Submission.EFL.Comm.UpperRegularPerfectMatching
import Submission.EFL.Comm.InternalMatchingConnect
import Submission.EFL.RegReservoir
import Submission.EFL.LowerReg
import Submission.EFL.Obs12
import Submission.EFL.Absorption
import Submission.EFL.CrossingAbsorption
import Submission.EFL.InternalAbsorption
import Submission.EFL.InternalStep
import Submission.EFL.InternalMain
import Submission.EFL.GFactorDischarge
import Submission.EFL.HugeStep
import Submission.EFL.HugeStep2
import Submission.EFL.DiffAbs
import Submission.EFL.DiffAbs2
import Submission.EFL.HugeAbsorption
import Submission.EFL.MultiHypergraph
import Submission.EFL.DegreeBounds
import Submission.EFL.ReservoirType
import Submission.EFL.DegreeLemma
import Submission.EFL.Regularising
import Submission.EFL.VplusBound
import Submission.EFL.EasyObs
import Submission.EFL.EGJ
import Submission.EFL.S12Setup
import Submission.EFL.S12Step4
import Submission.EFL.S12Step5
import Submission.EFL.S12Step6Aux
import Submission.EFL.S12Step6
import Submission.EFL.S12Step7
import Submission.EFL.Nibble
import Submission.EFL.S12Step8
import Submission.EFL.S12Step8r
import Submission.EFL.S12Mprev
import Submission.EFL.S12Step10
import Submission.EFL.S12Inst5
import Submission.EFL.S12Step9Pack
import Submission.EFL.S12Step9
import Submission.EFL.S12Numeric
import Submission.EFL.S12Assem
import Submission.EFL.S12Finish
import Submission.EFL.S12Core
import Submission.EFL.S12Final
import Submission.EFL.S12Step1Full
import Submission.EFL.S12Params
import Submission.EFL.Comm.S12NumericArith
import Submission.EFL.Comm.TwoMulLeRpowLog
import Submission.EFL.S12ANum
import Submission.EFL.S12MainA
import Submission.EFL.S12MainA2
import Submission.EFL.S12A2Main
import Submission.EFL.S12BNum
import Submission.EFL.S12MainB
import Submission.EFL.S12Assembly
import Submission.EFL.LeftoverProof
import Submission.EFL.LeftoverFinal
import Submission.EFL.AbsorberDeletion
import Submission.EFL.OptCol
import Submission.EFL.OptColOdd
import Submission.EFL.MainThm2
import Submission.Commons.Data.Real.exvol_arith
import Submission.Commons.Data.Real.ceil_sub_nat
import Submission.Commons.Combinatorics.FiniteSampling.exists_finset_sum_close
import Submission.Commons.Combinatorics.SimpleGraph.hall_based_finishing
import Submission.Commons.Combinatorics.Matching.upper_regular_exists_injective
import Submission.EFL.Embed
import Submission.EFL.EmbedProof
import Submission.EFL.Roadmap
import Submission.Deep.Reed
import Submission.Deep.NCP
import Submission.Work.Deep.Sparse.MolloyReed
import Submission.Work.Deep.Kahn.kahnRoundStatement
import Submission.Work.Deep.Nibble.NibbleFinal
import Submission.Work.Deep.GKO.OneFact.ConeWiring

open ErdosFaberLovaszConjecture
open Filter

set_option autoImplicit false
variable {V : Type*}

namespace Submission

/-!
# Erdős–Faber–Lovász: main theorem of Kang–Kelly–Kühn–Methuku–Osthus (Annals of Math. 198 (2023))

**Target statement (Theorem 1.1 of the paper).** For all sufficiently large `n`,
every *linear* hypergraph on `n` vertices has chromatic index at most `n`.

## Where the proof stands

`Submission/EFL/` contains the verified elementary infrastructure:

* `Basic.lean`       — colouring API and the chromatic index on the exact
                       `ChallengeDeps` definitions;
* `LineGraph.lean`   — edge-colourings of a hypergraph ↔ vertex-colourings of
                       its line graph;
* `Reformulation.lean` — the target theorem in its `∀ᶠ n in atTop` /
                       `∃ N, ∀ n ≥ N` / line-graph forms, all provably equivalent.
* `BigEdges.lean`     — the paper's opening reduction: it suffices to prove the
                       theorem for linear hypergraphs whose edges all have at
                       least two vertices (`eflStatement_of_bigEdges`), by
                       extending colourings of the large edges to singleton
                       edges (every vertex is in at most `n-1` large edges,
                       which use pairwise distinct colours).
* `Matching.lean`     — the paper's working definition of a colouring: colour
                       classes are *matchings*, and an `n`-colouring is the
                       same thing as `n` pairwise edge-disjoint matchings
                       containing all the edges
                       (`colorable_iff_hasMatchingDecomposition`);
                       a matching is an independent set of the line graph
                       (`isMatching_iff_isIndepSet`).
* `Counting.lean`     — pair double-counting in a linear hypergraph on
                       `n` vertices:
                       `∑_e |e|·(|e|−1) ≤ n(n−1)`
                       (`sum_edgeSize_mul_sub_le`) and, as a consequence, at
                       most `n(n−1)/(s(s−1))` edges of size at least `s`
                       (`card_edges_size_ge_le`).* `NeighbourSum.lean` — the §6.2 neighbour-sum engine (first line of the
                       proof of the paper's Prop `fwdnbr`): for a linear
                       hypergraph and an edge `e`, `∑_{f∈N(e)}(|f|−1) ≤
                       |e|·(n−|e|)` (`sum_neighbour_size_sub_le` and its
                       real cast `sum_neighbour_real_le`, via the cross-pair
                       machinery `crossPairs` / `neighbourCrossPairs` and
                       `neighbourCrossPairs_card`), with the subclass bounds
                       `card_neighbour_family_mul_le` / 
                       `card_neighbour_family_le`
                       (a subfamily of `N(e)` of members of size ≥ ℓ has
                       size ≤ |e|(n−|e|)/(ℓ−1)), used by the reordering
                       lemma; and **Prop `fwdnbr` is complete**
                       (`fwdnbr_inequality1`: `(1+α₁)m₁ + m₂/(1+α₂) ≤
                       n + (1+α₂)n/(r−1−α₂)`; `fwdnbr_inequality2`:
                       `m₁ ≤ (τ + (1+α₂)(1+α₂r)/(r−1−α₂))·n/α₁` given
                       `m₁+m₂ ≥ (1−τ)n`, `α₁ > 0`), assembled from
                       `fwdnbr_sum_alpha` (α), `fwdnbr_union_upper`,
                       `fwdnbr_beta` (β), `fwdnbr_gamma` (γ) and
                       `one_sub_inv_le`.
* `Reordering.lean`    — the §6.2 reordering lemma (`reordering-lemma`),
                       stated precisely (`ReorderingInstance`: linear, edges
                       ≥ r₁ ⇒ an ordering which is good — all `fwddeg ≤
                       (1−τ)n` — or admits a volume witness `W` with
                       size-similarity `WMaxSize`, volume `WVolume ≥
                       (1−τ−7τ^{1/4}/K)²/(1+3τ^{1/4}K⁴)`, and the
                       ordering properties `OrderingGoodness`(O1)/
                       `OrderingBySize`(O2)); the normalised volume
                       `Hypergraph.volume` with `volume_nonneg`,
                       `volume_mono`, `volume_le_one` (vol ≤ 1 for linear
                       hypergraphs); **Blocks I–III proved** — the
                       forward-degree walk (`blockI`, `AdmissiblePair`,
                       `predEdge`, `O1_of_pred`, `O2_of_pred`, …), the
                       size-non-increasing order (`sizeOrder`, …), and the
                       volume set `VolumeSet` with (W1)
                       (`volumeSet_maxSize`) and `blockIII_setup`; and
                       **Block IV fully proved** — the paper's eq. (6.3):
                       by the minimality of the prefix of `eStar` among
                       admissible pairs (`exists_minimal_admissible`,
                       `exists_minimal_admissible_of_fintype`), every
                       preceding neighbour `e` of `eStar` has
                       `|N(e)∩H^{⪯e*}| > (1−τ)n` (`blockIV_of_minimal`,
                       `minimal_admissible_dichotomy`); the proof is the
                       **block rotation** `rotateEquiv` (rank facts
                       `rot_of_lt`/`_between`/`_gt`,
                       `rotateVal_strict`/`rotateVal_reflect`,
                       `rotate_rank_le_b_iff`,
                       `rotate_rank_le_iff_of_gt_b`), the exact new
                       forward degree `fwddeg'(e) = |N(e)∩H^{⪯e*}|`
                       (`rotate_fwdnbr_eq_nbrsInPrefix`,
                       `rotate_fwddeg_e`), preservation of (O1)+(O2)
                       (`blockIV_O1`, `blockIV_O2`) and of edges past
                       `eStar` (`rotate_fwdnbr_of_rank_gt_b`), and the
                       prefix loss `blockIV_prefix`/`blockIV_prefix_card`
                       — `blockIV_rotation` packages the contradiction.
                       **Block V fully proved** — `XSmall` = `X`, eq. (6.4)
                       `blockV_X_bound` (`|X| ≥ (1−τ−2√τ/K)n`, margin
                       `1 ≤ τ(r−1)`) and eq. (6.5) `blockV_app2`
                       (`|(N(e)∩H^{⪯e*})∖W| ≤ 6τ^{1/4}n/K` for `e ∈ X`,
                       via `fwdnbr_inequality2` with `α₁ = K³τ^{1/4}`,
                       `α₂ = K√τ`, `sizeFactor_ge_product`,
                       `outsideVolumeSet_subset_big`, and the τ^{1/4} algebra
                       `blockV_app2_algebra`); **Block VI part 1 proved** —
                       `card_commonNeighbours_disjoint_le`
                       (`|N(f)∩N(g)| ≤ |f||g|` for disjoint `f,g`, eq. (6.8)'s
                       engine); Block VI part 2 (the `N₁`/`N₂` eq. (6.7)
                       counting, eq. (6.6), the double count, and the (W2)
                       volume bound) is the remaining work of the reordering
                       lemma, followed by the assembly of `ReorderingInstance`.)
* `EdgeSize.lean`     — the paper's edge classes (`small`/`medium`/`large`
                       by size thresholds, `FPP-extremal`, `huge`), as
                       sub-hypergraphs preserving linearity, covering the
                       edge set (`union_small_medium_large`).
* `ColourClassSplitting.lean` — the margin splitting engine for
                       `few-large-colour-classes`(ii): integer greedy chunking
                       of a matching edge list at the vertex-coverage
                       threshold `⌈αn/2⌉` (consecutive chunks of coverage
                       `∈ [⌈αn/2⌉, 2⌈αn/2⌉−1]` plus one leftover of coverage
                       `< ⌈αn/2⌉`), the partition of a colour class into
                       singleton/chunk/leftover pieces
                       (`SplitColourClassMarginStatement`,
                       `splitColourClassMargin`, exact-once
                       `splitColourClass_exactlyOnce`) and the threshold
                       bounds `SplitThreshold_lower/upper`.  (The def
                       `SplitColourClassStatement` recorded there is *false*
                       in corner cases and kept only as documentation.)
* `ColourClassSplitHonest.lean` — **the honest colour-class splitting
                       theorem** `splitColourClassHonest`: every colour class
                       splits into at most `2/α + 1` pairwise edge-disjoint
                       matching pieces, each a subfamily of the class and
                       either a single edge or covering `< αn + 1` vertices,
                       every edge in exactly one piece.  This corrects Prop
                       6.8's partition claim (the paper's "all pieces cover
                       ≥ αn/2, at most 2/α pieces" is false in corner cases:
                       e.g. a class of three disjoint `0.4αn`-edges); the
                       `+1` margin is absorbed downstream by splitting at a
                       halved parameter (`SplitPieceOK_half_strict`).
* `AlphaBoundedColouring.lean` — **the honest α-bounded recolouring
                       theorem** (`alpha_bounded_recolour`), Prop 6.8(ii)
                       (`few-large-colour-classes`(ii)): from any proper
                       edge-colouring `φ` of a linear hypergraph (all edges
                       ≥ r+1) using the colours of `C`, an β-bounded proper
                       edge-colouring exists with at most
                       `|C| + (2/(β/2)+1)·n/((β/2)r)` colours; big colour
                       classes (covering > βn/2) are split at the halved
                       parameter β/2 (`splitColourClassHonest` +
                       `SplitPieceOK_half_strict` absorbs the +1 margin),
                       small classes are kept.  Provides host-independent
                       `Coloring.AlphaBounded` and the
                       colouring-from-families device
                       (`colouringOfFamilies_fin_AlphaBounded`: a finite
                       family of pairwise-disjoint matching families that
                       covers every edge yields a colouring whose colour
                       classes are exactly the members).

* `GreedyListColouring.lean` — **Prop 6.9 fully proved** (paper §6.3):
                       ordering vocabulary (rank `ord : 𝓗 ≃ Fin k`,
                       `precedingDegree 𝓗 ord e` = `d⪯(e)`), the
                       `SegmentColourable` machinery with maximal colourable
                       prefix, the greedy extension steps — huge successor
                       (fresh colour; its class is a singleton) and small
                       successor (a colour outside `C₁ ∪ C₂`; `C₁` = colours
                       of coloured neighbours of the successor,
                       `|C₁| ≤ d⪯(f)`, `C₂` = heavy colours,
                       `|C₂| ≤ 2n/(α₂(r−1))` via Prop 6.8(i)) — the
                       transport of a colouring of the whole edge set back
                       to `𝓗`, the huge-first reordering of an arbitrary
                       ordering (`exists_hugeFirst_reorder`,
                       `fwddeg_le_of_reorder`: `fwddeg' ≤ fwddeg + #big`),
                       and the assembly `prop69_colouring` /
                       `prop69Instance`/`Prop69Instance`: for a linear
                       hypergraph with all edges of size `≥ r`, any ordering
                       and lists with `|C(e)| ≥ d⪯(e) + α₁n`, an
                       `α₂`-bounded proper edge-colouring respecting `C`
                       exists, under the margins
                       `2n/(α₂(r−1)) < α₁n/4` and `#big < α₁n/2`
                       (`#big` = number of edges of size ≥ α₂n/2).

* `ColourClassCounting.lean` — the bridge from the matching/colour-class
                       vocabulary to the family machinery: `EdgeSetFamily`
                       (a set of edges as a finite family of vertex sets),
                       lifting of matchings (`IsMatchingFamily_of_IsMatching`)
                       and colour classes (`classVertexCount_eq_FamilyVertexCount`),
                       and the paper's `few-large-colour-classes`(i) in
                       colour-class language
                       (`fewLargeColourClasses_of_colorClasses`,
                       `card_bigColourClasses_le`: at most `n/(αr)` colours
                       whose class covers ≥ αn vertices, when every edge has
                       size ≥ r+1).
* `FewLargeColourClasses.lean` — the first layer of the proof of Theorem 6.7
                       (Proposition `few-large-colour-classes`, §7): family
                       vocabulary (`sumEdgeSizes`, `familyNatVolume`,
                       `familyVolume`), the lower bound on a family's volume
                       in terms of its covered-vertex sum
                       (`familyNatVolume_ge_mul_sum`), `familyVolume_le_one`
                       for subfamilies of a linear hypergraph, and the bound
                       `fewLargeColourClasses_bound` / `fewLargeColourClasses_le`
                       on pairwise edge-disjoint matchings each covering
                       ≥ αn vertices with edges of size ≥ r+1
                       (`t·αr ≤ n−1`, hence `t ≤ n/(αr)`).
* `ClassicalBounds.lean` — **the classical bounds proved unconditionally**:
                       `colorable_two_mul_add_one` /
                       `chromaticIndex_le_two_mul_add_one` (`χ′ ≤ 2n+1` for
                       every linear hypergraph on `n` vertices) and
                       `colorable_of_min_edgeSize` (`χ′ ≤ (1+1/(r₁−1))n+1`
                       when all edges have size `≥ r₁ ≥ 2`), via the greedy
                       lemma `colorable_of_precedingDegree_le` and the
                       size-order bounds `precedingDegree_sizeOrder_le` /
                       `precedingDegree_sizeOrder_le_le_one`.
* `LocallySparse.lean` — §6.2's locally-sparse-graph colouring corollaries
                       reduced to the two deep inputs (`MolloyReedStatement`
                       = paper Thm 6.4, `AKSStatement` = paper Thm 6.6), with
                       all the line-graph counting proved
                       (`card_neighbourEdges_le` = `Δ(L)` bound,
                       `card_commonNeighbours_le` = codegree bound,
                       `nbrEdges_lineGraph_le`, `lineGraph_maxDegree_le`)
                       and the two corollaries `corollary_6_5`
                       (`χ′(H) ≤ (1−ζ/500)n`) and `corollary_6_7`
                       (`χ′(H) ≤ εn`) proved from them, with the paper's
                       hierarchies isolated in `Corollary65Margins` /
                       `Corollary67Margins`.
* `ColourCombine.lean` — **combining colourings of a partition**: if
                       `𝓖₁, 𝓖₂ ⊆ 𝓗` cover `𝓗`, then colourings of `𝓖₁` with `a`
                       colours and of `𝓖₂` with `b` colours combine into one
                       of `𝓗` with `a+b` colours (`Hypergraph.Colorable.union`),
                       and the three-part version `Colorable.union3` (the
                       shape of the theorem-1.3 decomposition
                       `𝓗 = 𝓗₁ ∪ 𝓗₂ ∪ 𝓗₃`).
* `DeepInputs.lean`   — the external deep inputs as `Prop`-valued *input
                       statements*, together with the hypergraph degree
                       vocabulary: `hypergraphDegree`/`hypergraphMaxDegree`
                       (`d_𝓗(v)`, `Δ(𝓗)`) with monotonicity under
                       subfamilies, and `KahnStatement` (the paper's
                       Theorem 4.6, Kahn's asymptotically optimal
                       list-edge-colouring theorem) with its list-free
                       consequence `kahn_colorable` — the form used to colour
                       the small/medium edges in Theorem 1.3 and Theorem 6.1.
* `SubfamilyConcat.lean` — **concatenating orderings of a disjoint cover**
                       (the bookkeeping behind Theorem 1.3's
                       `W₁,…,W_{k-1}, 𝓗₁^good,…` and Figure 3's
                       `𝓗₃, W₂, 𝓗₂^good, 𝓗₁^good`): `setSumEquiv` (a disjoint
                       cover is a sum, with the cardinality identity
                       `natCard_eq_add_of_cover`), the concatenated ordering
                       `concatOrderingS` with its rank characterisations
                       (`concatOrderingS_lift₁_lt`, `_lift₂_ge`, the `le_iff`
                       comparisons), and the exact preceding-degree
                       transfer `precedingDegree_concatOrderingS_of_mem` /
                       `_of_notMem`, packaged as
                       `exists_ordering_of_disjoint_cover`: the cover has an
                       ordering with `d⪯ ≤ b` as soon as each part has one
                       (for the second part counting also the members of the
                       first part that meet the edge).

* `StabilityLoop.lean` — **the loop of Theorem 1.3** (in progress): the
                       subfamily-level volume bookkeeping (`finFam`, with
                       `volume_finFam` identifying the `𝓗`-finset volume
                       with the subfamily volume, `volume_subfamily_mono`,
                       `volume_subfamily_union`), the three blocks of one
                       reordering step (`rankBelow ord fStar` = the paper's
                       `𝓗_i^left`, `midBlock ord fStar eStar` = the middle
                       interval `[f*, e*]` = the volume block `W_i`, and
                       `goodBlock ord eStar` = `𝓗_i^good`), with membership/
                       subset/disjointness lemmas, the cover
                       `cover_blocks`, (O1) on the good block
                       (`goodBlock_precedingDegree_le`), (O2) on the middle
                       block (`midBlock_size_ge`), the step-data extraction
                       `exists_step_data` (from a `VolumeWitness`: the size
                       bounds `|e*| ≤ |e| ≤ A|e*|` on the middle block and
                       the volume bound `vol([f*,e*]) ≥ volBound τ K`), and
                       `exists_restricted_ordering` (the induced ordering of
                       a subfamily has no larger preceding degrees, via the
                       commons lemma `Commons.Data.Finset.restrict_ordering`).
                       Remaining here: the list-indexed decomposition
                       structure and the induction on the volume, then the
                       Theorem-1.3 assembly (AKS on the blocks, Prop 6.9 on
                       the good part, `Colorable.union3`).

* `WeakStability.lean` — Theorem 1.3 (weak stability) of the paper: the
                       real-threshold edge classes
                       (`sizeLE`/`sizeGE`/`sizeBetween`, `cover_size_classes`),
                       the one-colour-per-edge bound
                       (`colorable_of_card_le`), the linear-hypergraph size
                       count `card_sizeGE_le`, the `𝓗₂` colouring from Kahn's
                       theorem (`colorable_sizeLE_of_kahn`), the `𝓗₃`
                       colouring (`colorable_sizeGE`), the AKS-based colouring
                       of a volume block (`colorable_block_of_aks`,
                       `colorable_block_of_decomposition`), the colouring of
                       the good part by Prop 6.9
                       (`colorable_good_of_ordering`), the list-union
                       bookkeeping (`famUnion`, `volume_famUnion`,
                       `volume_sum_le_one`, `famUnion_colorable`,
                       `pairwise_map_sub`) and the numeric vocabulary of the
                       constant hierarchy (`one_le_inv_pow`,
                       `inv_pow_le_inv_pow`, `inv_ge_1000`, `two_mul_le_pow`,
                       `one_add_four_mul_sq_le_pow`, `div_pow_eq_mul`), plus
                       the statement `WeakStabilityInstance ε`.
* `WeakStabilityMain.lean` — **Theorem 1.3 of the paper, proved** (modulo the
                       two stated deep inputs `KahnStatement` and
                       `AKSStatement`): `weakStability_of_deep (hK) (hAKS) (ε)
                       (hε0) : WeakStabilityInstance ε`.  The long numeric
                       preparation is split into the top-level lemmas
                       `weakStability_margins` (`ReorderingMargins r₁ τ K`),
                       `weakStability_sizeFactor_le`, `weakStability_Csf2`,
                       `weakStability_Csf3`, `weakStability_volBound_ge`,
                       `weakStability_hc2`, `weakStability_hc3` and
                       `weakStability_hfinal`, each checked in a small local
                       context; `weakStability_small` (the case `ε ≤ 1/1000`)
                       then assembles them with the `H₁` (loop), `H₂` (Kahn)
                       and `H₃` (huge edges) colourings and
                       `Colorable.union3`, using the budget
                       `εn/4 + (εn/10 + M) + (εn/3 + 1) + εn/4 ≤ εn`
                       (with `M + 1 ≤ εn/24`).  The constants are
                       `τ = 1 − ε/6`, `K = ⌈(1/ε)²⌉₊`, `η = ζc/ε¹⁰`,
                       `r₁ = ⌊1/η⌋₊ + 1`, `M = ⌈1/volBound τ K⌉₊ + 1`,
                       `εb = ε/(10M)`, `Δ = 4ε^{−10}n`.
                       (Superseded draft: `Submission/EFL/WeakStabilityAssembly.txt`.)
* `LargeEdgeSetup.lean` — the App-1 ingredients of Theorem 6.1: the
                       constants `τ₁ = 1 − γ₂/3`, `K₁ = ⌈(2γ₂)⁻²⌉₊`, the
                       reordering margins `app1_margins`, the firing
                       `app1_firing`, and the two numeric bounds used in
                       Figure 3: `app1_sizeFactor_le`
                       (`sizeFactor τ₁ K₁ ≤ γ₂^{-10}`, i.e. `(W₁1)`) and
                       `app1_volBound_ge` (`volBound τ₁ K₁ ≥ γ₂^{20}`, i.e.
                       `(W₁2)`), together with `app1K_le`,
                       `app1K_pow_four_le`.
* `MedEdges.lean`      — the paper's `Δ(𝓗) ≤ n/(r₁−1)` for linear hypergraphs
                       (`degree_mul_le`, `degree_le_div`, `maxDegree_le_div`:
                       the other-vertex sets of the edges through a vertex
                       are pairwise disjoint), Proposition 6.10
                       (`medEdges_colouring_of_chi`): a `γ`-bounded proper
                       edge-colouring with at most `γn` colours for a linear
                       hypergraph all of whose edges have size ≥ r₁, and
                       `colorable_of_kahn_sizes` (the chromatic-index input
                       `χ' ≤ 4n/r₁ + 1` from `KahnStatement`).
* `Commons.Combinatorics.SimpleGraph.vizing` — **Vizing's theorem** for
                       simple graphs (`G.lineGraph.Colorable (G.maxDegree+1)`,
                       i.e. `χ'(G) ≤ Δ(G)+1`), proved and committed to the
                       shared commons with minimal imports (usable from this
                       development): the edge-colouring input of §5
                       (FPP-extremal hypergraphs) and of §12.
* `LargeEdgeCase1.lean` — **Case 1 of Theorem 6.1 proved**: given a good
                       ordering of the large edges (all preceding degrees
                       `≤ (1−2σ)n`), the non-extremal alternative
                       `LargeEdgeNonExtremal` holds (`largeEdge_case1`).
                       The large edges are coloured by Proposition 6.9
                       (`largeEdges_colouring_of_prop69`), the medium edges
                       by Proposition 6.10, and the two colourings are
                       combined by `coloringUnionOfCover`
                       (`largeEdge_nonExtremal_of_colourings`), with the
                       properties (6.1:a)(i)–(iii) verified (huge classes
                       are singletons, `Cmed`-classes cover few vertices,
                       all other unassigned classes cover `≤ βn`).
                       Also the huge-edge counts `card_huge_le` /
                       `natCard_hugeEdges_le`: a linear hypergraph on `Fin n`
                       has at most `32/β²` edges of size `≥ βn/4` (the
                       pair-counting form of the paper's (2.2), used for
                       `e(𝓗_huge)`).
* `ReorderingSplit.lean` — **one application of the Reordering Lemma split
                       into the Figure-3 shape** (`reordering_split`): for a
                       subfamily `𝓖 ⊆ 𝓗` of a linear hypergraph with all
                       edges `≥ r₁` and the margins `ReorderingMargins r₁ τ K`,
                       an ordering `ord : 𝓖 ≃ Fin k`, a partition
                       `𝓖 = Good ⊔ Left` (`Left` = the `⪯e*`-prefix, `Good`
                       = the rest), a threshold `r₂ = |e*|` with
                       `|e| ≥ r₂` on `Left`, and a volume set `W ⊆ Left`
                       (empty in the good case, `vol(W) ≥ volBound τ K`
                       otherwise) with `|e| ≤ sizeFactor τ K · r₂` on `W`.
                       Also `app3_good_of_disjoint` — the App-3 conclusion
                       (`d⪯ ≤ n/2000` on the residual family `𝓖₃`) in the
                       disjoint-subfamilies form used when
                       `𝓗₃ = (𝓗₁^left ∖ W₂) ∪ 𝓗_huge`.
* `Fig3Blocks.lean`   — **concatenating the blocks of Figure 3**
                       (`exists_ordering_of_three_blocks`): for pairwise
                       disjoint subfamilies `A`, `B`, `C` covering `𝓗`, with
                       orderings of each, the concatenation `A → B → C` gives
                       an ordering of `𝓗` whose preceding degrees are
                       bounded by `b` whenever the per-block bounds of
                       Figure 3 hold (`A` counts nothing extra, `B` adds the
                       edges of `A` meeting the edge, `C` adds those of
                       `A ∪ B`).  Uses `exists_ordering_of_disjoint_cover`
                       twice.
* `Fig3Case1.lean`    — **Figure 3's Case 1 end-to-end**:
                       `exists_goodOrdering_of_app1_app2` builds, from the
                       App-1 split of `𝓗' = 𝓗 ∖ 𝓗_huge` and a *good*
                       ordering of `𝓗₁^left`, an ordering of `𝓗` in which
                       every preceding degree is at most `(1−2σ)n` (the
                       three blocks `𝓗_huge → 𝓗₁^left → 𝓗₁^good` with the
                       paper's (b)–(d) bookkeeping);
                       `largeEdge_nonExtremal_of_app1_app2` combines it with
                       `largeEdge_case1` to obtain `LargeEdgeNonExtremal`;
                       and `app1_split` fires the Reordering Lemma on
                       `nonHuge 𝓗 β` with the App-1 numeric bounds
                       (`γ₂ n/3` on the good part, `γ₂^{20}` volume,
                       `γ₂^{-10}` size factor), and `app2_margins`
                       (`ReorderingMargins r₁ (3σ) 1` for `r₁ ≥ R(σ)`,
                       via the commons lemma
                       `Commons.Analysis.Real.reordering_threshold`).
* `ColourUnion.lean`  — combining two edge-colourings with disjoint colour
                       sets on a cover (`coloringUnionOfCover`), with the
                       exact transfer of colour classes and covered vertex
                       sets to the two parts.
* `ColourCombine2.lean` — relabelling colourings (`Coloring.map`,
                       `exists_coloring_usesColourSet`: a colouring can be
                       moved into any prescribed colour set of at least the
                       same size, preserving `AlphaBounded`), the
                       combination `coloringUnionCross` of two colourings of
                       a cover under the *cross-condition* (no colour is used
                       by both parts on intersecting edges; the colour sets
                       need not be disjoint), the class-vertex count
                       `classVertexCount_coloringUnionCross_le` and the
                       bounded-class bound
                       `classVertexCount_le_of_alphaBounded`; and the
                       Case-2 assembly `largeEdge_nonExtremal_of_largeColouring`
                       (the non-extremal alternative from a large-edge
                       colouring whose huge colour classes are singletons and
                       whose other classes cover at most `βn` vertices).
* `LargeEdgeBlocks.lean` — **the App-1/App-2 block decomposition of Figure 3**:
                       `BlocksOK` records the data of two firings of the
                       Reordering Lemma (the splits
                       `𝓗' = 𝓗₁^good ⊔ 𝓗₁^left` and
                       `𝓗₁^left = 𝓗₂^good ⊔ 𝓗₂^left`, the thresholds `r₂, r₃`,
                       the volume set `W₂`, the residual family
                       `𝓗₃ = 𝓗_huge ∪ (𝓗₂^left ∖ W₂)` and the partition
                       `𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good` of
                       `eq:large-edge-thm-partition`), and
                       `exists_largeEdgeBlocks` is the firing theorem.
* `LargeEdgeCase2.lean` — the Case-2 splitting of the large edges
                       (`case2Left`/`case2Right`, `case2_parts`: the two
                       halves partition `𝓗_large`) and the bound
                       `card_hugeColours_le` on the number of colours a
                       colouring assigns to its huge edges (`≤ 32/β²`), the
                       set `C_huge` of Case 2.1; and
                       `sparse_colouring_usesColourSet` — Claim
                       `claim:sparse-colouring` of the paper: a locally sparse
                       linear hypergraph (Corollary 6.5) can be coloured
                       `β'`-boundedly using any prescribed colour set of size
                       `(1−ζ/1000)n`; and `app3_goodOrdering_of_volume` — the
                       App-3 step of Figure 3 in subfamily-volume form (a
                       disjoint subfamily `𝓖₂ ∋ W₂` of volume `≥ 1−δ³` forces
                       the complementary subfamily `𝓖₃` to admit an ordering
                       with all preceding degrees at most `n/2000`).
* `Nearfull/` — the **minimal-import port of the whole §5 chain** of the
                       paper (Lemma 5.1, `extremal-case-lemma`, and its
                       supporting files: maximal disjoint pairings, useful
                       pairs, the clique case, the size-`k` family and the
                       1500-line `linear_nearfull_colouring` itself).  The
                       commons versions of these files start with
                       `import Mathlib` and are therefore unusable here
                       (they export `_root_.Hypergraph`, which makes the
                       fixed `Solution.lean`'s unqualified `Hypergraph`
                       ambiguous); the modules `Submission.EFL.Nearfull.*`
                       contain the *same declarations* (same names and
                       namespace `Commons.Combinatorics.Hypergraph`, same
                       proofs) with imports minimized by Mathlib's
                       `#min_imports`.  `LinearNearfullColouring.lean`
                       provides `Commons.Combinatorics.Hypergraph.linear_nearfull_colouring`.
* `LargeEdgeCases.lean` — **the case split of Theorem 6.1**: `case1_of_blocks`
                       (the App-2 firing is good: `W₂ = ∅` forces
                       `𝓗₂^left = ∅` and the non-extremal alternative follows
                       from the good ordering) and `largeEdge_of_blocks`,
                       which performs the full split — Case 1 (`W₂ = ∅`),
                       Case 2.1 (`r₃ < (1−δ)√n`, via `case2_nonExtremal`)
                       and Case 2.2 (isolated as the explicit hypothesis
                       `h22`, the paper's extremal alternative).
* `LargeEdgeCase22.lean` — **Case 2.2 of Theorem 6.1 begun**: the volume bound
                       `volume_singleton` and the conversion of a volume
                       bound into an edge-size bound
                       (`edgeSize_le_half_mul_of_volume`,
                       `volume_singleton_le_of_notMem`,
                       `edgeSize_le_half_mul_of_blocks`); the FPP-extremal
                       volume witness of the case (`extremal_witness_of_blocks`,
                       giving the first conjunct of `LargeEdgeExtremal` with
                       `W := W₂`); the colour-class coverage lemmas
                       (`sumEdgeSizes_le_of_card_le`,
                       `card_EdgeSetFamily_colorClass_le`,
                       `classVertexCount_le_of_ncard_le`,
                       `classVertexCount_le_two_mul`,
                       `case22_left_classes_le`); and Lemma 5.1 in the
                       colouring API (`NearfullColouring`,
                       `nearfullColouring_exists`, `nearfull_colouring_of`,
                       `case22_left_colouring`, `case22_classVertexCount_le`);
                       the `r₂ ≥ 2r₀` derivation
                       (`r₀_lt_r₂_of_blocks`) and its consequence
                       `medEdges_subset_good₁` (`𝓗_med ⊆ 𝓗₁^good`).
* `LargeEdgeCase22Main.lean` — **CASE 2.2 OF THEOREM 6.1 IS COMPLETE.**
                       The three blocks of Figure 3 in the extremal regime
                       (`𝓗_huge ∪ 𝓗₂^left`, `𝓗₂^good`, `𝓗₁^good`) are
                       recoloured: the block decomposition
                       (`case22_hugeLeft_subset`, `case22_cover`,
                       `case22_disjoint_hugeLeft_good₂/_good₁`) and the
                       size bound `|e| ≤ δn/2` for every edge
                       (`case22_noBig`); the two Proposition 6.9 firings
                       (`case22Forb₁`/`case22Forb₂`/`case22List₂`/`case22List₃`
                       with their list bounds `case22_fwddeg_good₂`,
                       `case22_fwddeg_good₁`, `case22_list_bound₂`,
                       `case22_list_bound₃`); the colour set
                       `C_med ⊆ univ ∖ C_huge` of size `⌊γ₂n⌋`
                       (`case22_exists_Cmed`); the glue by two applications
                       of `coloringUnionCross` and the three colour-class
                       estimates (`case22_colouring`); and the resulting
                       alternative `case22_extremal`.  Finally
                       `largeEdge_of_blocks_full` is the case split of
                       Theorem 6.1 with the Case-2.2 obligation `h22`
                       discharged.  The fourth sub-case (`W₂ ≠ ∅`,
                       `r₃ ≥ (1−δ)√n`, `r₃ > √(n/(1−4σ))`) is handled by the
                       pair count (`case22_left_card_le`), which shows the
                       App-2 ordering is good (`case22_good_ordering`), so
                       that `case1_of_blocks_of_good` applies — this supplies
                       the paper's `eqn:d3-upper-bound`.  `r₂ ≥ γ₂^{10} r₃`
                       (`r₂_ge_r₃_of_blocks`) is likewise *proved*, from the
                       intersection `W₁ ∩ W₂ ≠ ∅` of the two Reordering-Lemma
                       volume sets (whose volumes would otherwise exceed one)
                       — this is why `BlocksOK` now records the App-1 volume
                       set `W₁` with its `(W1)`-properties.  **The case
                       analysis of Theorem 6.1 is complete**, modulo the
                       numeric hierarchy of its margins (explicit
                       hypotheses).
* `Case21.lean` — **CASE 2.1 OF THEOREM 6.1 IS DISCHARGED.**  The paper's
                       Case 2.1 uses the instance-dependent parameter
                       `ζ := 1 − r₃/√n` (which satisfies `ζ > δ`), and all the
                       `ζ`-dependent hypotheses of `case2_nonExtremal` are
                       produced here from `δ`-based margins that hold for all
                       large `n`: the four `Corollary65Margins` fields at
                       `B₀ := ⌈sizeFactor (3σ) 1·r₃⌉₊`, `Δ := (1 + δ/10⁵)n`
                       (`case21_margin_Dge`, `case21_margin_Dthr`,
                       `case21_margin_hcodeg`, `case21_margin_hfinal`), the
                       room/budget transfers (`Nat.ceil_le` + `omega`),
                       `hsize₃`, and the assembly `case2_nonExtremal'`.
                       The `3%` slack `1/500 + 1/10⁵ ≤ 5/(6e⁶)` between the
                       Molloy–Reed loss and Corollary 6.5's `1/500` is proved
                       from `Real.exp 6 ≤ 414`.  `MolloyReedStatement` now
                       also records that the threshold is bounded by a
                       polynomial in `1/ζ` (the content of `0 < 1/Δ ≪ ζ ≤ 1`),
                       which is what makes the instance-dependent `ζ`
                       usable.
* `Case21Margins.lean` — the `δ`-based numeric margins consumed by
                       `case2_nonExtremal'`: `gamma_seven_div_le`,
                       `margin_alphaδ` (`3τ^{1/4}(3σ) ≤ δ/10⁷`), `margin_k2δ`,
                       `margin_2σδ`, `margin_hnbig2`, `margin_sqrt4`,
                       `margin_σsmall2`, `margin_room1C`, `margin_room2C`,
                       `margin_budgetC`, `margin_marginAδ`.
* `LargeEdgeHierarchy.lean` — **the parameter hierarchy of Theorem 6.1 in
                       progress**: the counting bound `bigFinset_card_le`
                       (`#(bigFinset α₂ 𝓖) ≤ 8/α₂²` in a linear family), the
                       threshold constants `δThr`/`σThr` and the
                       parameter-only margin lemmas (`app3_volBound_ge`,
                       `tauQuarter_three_sigma_le`, `volBound_three_sigma_ge`,
                       `sizeFactor_three_sigma_le`, `app1_volBound_gt`,
                       `δThr_le_app3`), and the `n`-margin lemmas
                       (`margin_sq_mul`, `margin_sqrt`, `margin_huge`,
                       `margin_roomNat`, `margin_bigFinset`,
                       `bigFinset_eq_empty_of_nonHuge`, `margin_gamma2n`,
                       `margin_r0h`, `margin_bigcase`, `margin_sigma_n`,
                       `margin_beta_n`, `margin_two_beta5`, `margin_r0_lt`,
                       `margin_gamma_m`, `margin_A2`, `margin_slack`, and the
                       colour-budget margins `margin_room1`, `margin_room2`,
                       `margin_budget0`, `margin_Kroom`, `margin_C1K`).  The
                       threshold constants `ζc`, `γ₁Thr`, `βThr`, `R₀Thr`,
                       `R₁Thr`, `N₀Thr` are defined together with their basic
                       properties (`σThr_le`, `γ₁Thr_le`, `βThr_le`,
                       `N₀Thr_pos`, `R₀Thr_pos`, `R₁Thr_pos`, `ceil_le_of_le`,
                       `LargeEdgeExtremal_mono_γ₂`), and the medium-edge
                       colouring of §6 is proved from Kahn's theorem
                       (`medEdges_colouring_of_kahn`), and the trivial
                       (distinct-colour) colouring of `𝓗₃∖𝓗_med` used in the
                       `k ≤ (ζ/1000−2σ)n` branch of the paper's Case 2.1 is
                       `case2_H3med_distinct`; the `r₀`-ratio margins are
                       `margin_m22₂`, `margin_margin`, `margin_69m`,
                       `margin_69mσ`, `margin_marginA`, and the empty
                       hypergraph is handled by `largeEdgeNonExtremal_empty`.
                       The paper's `k`-split of Case 2.1 is now available:
                       `volume_ge_card_mul_sq`, `volume_H3_le`,
                       `r₃_lt_sqrt_of_k_large` (the volume computation
                       `k > (ζ/1000−2σ)n ≥ 2δ²n ⟹ r₃ < δ^{1/4}√n`, i.e.
                       `eqn:d3-upper-bound`'s companion estimate) and
                       `case2_H3med_split` (the `𝓗₃∖𝓗_med` colouring:
                       distinct colours when `k` is small, the App-3 greedy
                       colouring otherwise).  The assembly of
                       `LargeEdgeThmStatement` (choosing `δ₀, σ₀, γ₁₀, β₀,
                       R₁, R₀, N₀` and discharging the `n`-margins) is in
                       progress; the elaborated draft is kept in
                       `Submission/EFL/LargeEdgeHierarchyWIP.txt`.
* `LargeEdgeThm.lean`  — **THEOREM 6.1 (`large-edge-thm`) IS NOW PROVED**
                       (Theorem 6.7 of the paper) from the deep inputs
                       Molloy–Reed and Kahn and from Lemma 5.1:
                       `largeEdgeThmStatement_of_deep : MolloyReedStatement →
                       KahnStatement → LargeEdgeThmStatement` is
                       machine-checked and axiom-clean.  The module contains
                       (a) `largeEdgeInstance_of_thresholds`, the
                       per-instance layer: with the threshold hierarchy
                       `δ ≤ δThr γ₂`, `σ ≤ σThr δ`, `γ₁ ≤ γ₁Thr σ`,
                       `β ≤ βThr γ₁`, `R₁Full ≤ r₁`, `R₀Full ≤ r₀`,
                       `N₀Full ≤ n` it fires `exists_largeEdgeBlocks`,
                       colours the medium edges via Kahn
                       (`medEdges_colouring_of_kahn`), discharges all
                       ~74 numeric margins with the `margin_*` lemmas and
                       applies `largeEdge_of_blocks_full`; and (b) the
                       threshold layer choosing `δ₀, σ₀, γ₁₀, β₀, R₁, R₀,
                       N₀` in the order of the paper's `≪`-hierarchy.
                       New numeric tools: `margin_hfac`, `margin_m22₃`,
                       `margin_bigFinset_ratio`, `kahn_two`,
                       `γ₁Thr_le_quarter`, `σThr_le_inv_million`,
                       `δThr_le_self`.
* `Pow2Edges.lean`   — the dictionary between a family of 2-element edges and
                       the graph it represents: the "other vertex" of a 2-edge
                       (`otherVertex`, `otherVertex_mem`/`_ne`/`_unique`,
                       `eq_pair_otherVertex`, `otherVertex_pair`), the degree
                       identity `ncard_nbrs_eq_hypergraphDegree`
                       (`#(edges through v) = d_G(v)`), the neighbourhood
                       identity `ncard_inter_nbrs_eq`
                       (`|X ∩ N_G(v)| = #(edges through v with other end in
                       X)`), and the crossing identity
                       `edgeCount_eq_edgesBetween` (`edgeCount` — which
                       counts ordered pairs — equals the number of edges
                       between two disjoint vertex sets, for a family of
                       2-edges).
* `ReservoirExistence.lean` — **Proposition 11.1 (`prop:pseudo_reservoir`)
                       IS PROVED**: the existence of the pseudorandom
                       reservoir.  `exists_pseudoReservoir_eventually` states
                       that for `0 < ρ ≤ 1`, `ξ > 0` there is `N` such that
                       for `n ≥ N`, every linear `𝓗` on `Fin n`, every
                       `G' ⊆ 𝓗^{(2)}` and every family `𝓥` of at most
                       `n^{log n}` subsets of the vertex set, there is
                       `R ⊆ E(G)` with `d_R(v) = ρ d_G(v) ± ξn` for all `v`
                       and such that `R ∩ G'` is a `(ρ,ξ,ξ,ε)`-absorber for
                       `𝓥` which is also lower `(ρ,ξ,G')`-regular.  The
                       ingredients: the three event families (`starEv`,
                       `pairEv`, `crossEv`) with their cardinalities
                       (`card_starEv`, `card_pairEv`, `card_crossEv`), the
                       index type `ResIdx` with `resEv`/`resTol`, the
                       probabilistic method `exists_reservoir_core` (a direct
                       application of the commons sampling lemma
                       `exists_finset_sum_close`), the union-bound estimate
                       `reservoir_sum_bound` (with the two Chernoff exponent
                       comparisons `exp_bound_linear`, `exp_bound_quadratic`)
                       and the disjointness/number bound `card_pairs_le`
                       (`#(Finset (Fin n)²) = 4ⁿ`); the final numeric step is
                       the commons lemma
                       `Commons.Analysis.Real.reservoir_union_bound`.
* `GFactor.lean`      — the deep input `GFactorStatement` (**Lovász's
                       `(g,f)`-factor theorem**, the paper's
                       `thm:gf_factor`) as a `Prop`-valued input statement,
                       together with the induced-subgraph vocabulary
                       `nbrsIn`/`degIn` used to state it on a vertex set.
* `GFactorDischarge.lean` — **`GFactorStatement` IS DISCHARGED**: the theorem
                       `gfactorStatement : GFactorStatement` is proved from the
                       ported commons proof of Lovász's `(g,f)`-factor theorem
                       (`Commons.Combinatorics.LovaszGFactor.lovasz_gf_factor`).
                       The port lives in `Submission/EFL/Comm/`
                       (`BarrierCountGF`, `AltWalkFlipDegree`,
                       `GfFactorOfTight`, `GfFactorTight`, `LovaszGfFactorNat`,
                       `LovaszGfFactor`, all with minimal Mathlib imports), and
                       the discharge transports the statement of the theorem
                       to the induced graph `graphOf G W` of `GFactor.lean`
                       (`natCard_graphOf_adj`, `edgesOf`, `degIn_edgesOf`).
* `HugeStep.lean`     — §7.3 (`huge-edge-absorption-lemma`), part 1: the
                       margins `HugeMargins`, the crossing degree bounds and
                       the crossing step `huge_cross_step`, and the internal
                       degree bound `huge_internal_degree` with the internal
                       matching `huge_internal_matching`.
* `VplusBound.lean`   — **Claim 12.1 (EP3), first part IS PROVED**: for a
                       linear `𝓗`, a family `W ⊆ 𝓗` of edges of size `≥ 3` with
                       `∑_{e ∈ W} |e|(|e|-1) ≥ (1-δ)n(n-1)` and a set `U` of
                       vertices of `G`-degree `≥ (1-ε)n`, we have
                       `|U| ≤ 2δn` (`card_Vplus_le_of_extremal`), via the
                       handshake identity `∑_w d_G(w) = ∑_{e ∈ G} |e|`
                       (`sum_degAt_eq_sum_ncard`) and the bound
                       `∑_{w ∈ S} d_G(w) ≤ 2·e(G)`
                       (`sum_degAt_le_two_mul_card`).
* `EGJ.lean`          — the Ehard–Glock–Joos input of §8 (`thm:egj`) and its
                       sparsified corollary (`cor:sparse_egj`) as
                       `Prop`-valued statements `EGJStatement` /
                       `SparseEGJStatement`, together with the degree sum
                       `degreeSum`, in the style of `KahnStatement`.
* `EasyObs.lean`      — **Claim 12.1 (EP4) IS PROVED** as `easyObs_EP4`: in a
                       Type A colouring of the medium and large edges of a
                       linear hypergraph, at most one colour class contains a
                       huge edge and is difficult; the proof also provides
                       `classVertices_eq_of_colorClass_singleton` (a colour
                       class consisting of a single edge covers exactly the
                       vertices of that edge) and the family
                       `colorClassFam`.
* `MultiHypergraph.lean` — linear multi-hypergraphs (Definition 11.4's
                       `𝓗_reg` and the `𝓗'` of Lemma 11.3): a family of edges
                       of size at least two together with the multiplicities
                       of the singleton edges, with degrees
                       (`MultiHypergraph.deg`), order, `regHypergraph` and
                       `addSingletons`.
* `DegreeBounds.lean` — degrees of families of edges: `hdeg_sdiff`,
                       `hdeg_union`, `hdeg_eq_degAt` (for a family of
                       2-element sets the number of edges through `w` equals
                       `|N_R(w)|`), `degAt_le_pred` and the splitting
                       `hdeg_eq_small_add` of a degree into the edges of size
                       at most `r₁` and the rest.
* `ReservoirType.lean` — Definition 11.2: the three types of reservoirs
                       `IsReservoirTypeA1`, `IsReservoirTypeA2`,
                       `IsReservoirTypeB`, and the fact that the
                       neighbourhood in `G'` of a vertex of `U` is its
                       neighbourhood in `G`.
* `DegreeLemma.lean`  — **LEMMA 11.3 (`lem:degree-lemma`) IS PROVED** in the
                       core form `regularising_lemma_core`: the case analysis
                       of the paper (one degree estimate for each reservoir
                       type, `hdeg_sdiff_le_A` and `hdeg_sdiff_le_B`), the
                       choice `k = ⌊(1-ρ)(n-1) - βn/2⌋` and the verification
                       of the three conclusions (`𝓗'` is obtained from
                       `𝓗_small ∖ R_res` by adding `k - d(w)` singletons at
                       every vertex with `d(w) < k`, `𝓗' ⊆ 𝓗_reg` and
                       `d_{𝓗'}(w) = (1-ρ)(n-1 ± βn)`).
* `Regularising.lean` — **LEMMA 11.3 IN FULL** (`regularising_lemma`): the two
                       numerical inputs of the core (`hdeg_sdiff_pow2_le`,
                       the estimate `d_{𝓗∖E(G)}(w) ≤ (n-1-d_G(w))/2`, and
                       `hdeg_sub_small_le`, `d_𝓗(w) - d_{𝓗_small}(w) ≤ 2n/r₁`)
                       are discharged from the commons lemmas
                       `Commons.Combinatorics.Hypergraph.{card_size_ge_three_mul_two_le,
                       card_size_gt_mul_le, card_two_edges_eq_card_nbrs}`.
* `DiffAbs.lean`      — the pairing constructions of §7.4 (a complete graph on
                       `V^{(n-1)}` and the partner edge outside `U₁ ∪ e`).
* `DiffAbs2.lean`     — **LEMMA 7.12 (`difficult-edge-absorption`) IS PROVED**
                       as `difficult_edge_absorption`: for a linear hypergraph
                       without singleton edges and a huge edge `e`, either
                       `{e}` extends (by `𝓗^{(2)}`-edges) to a matching
                       covering `V^{(n-1)}(𝓗)` and all but five vertices of
                       `V^{(n-2)}(𝓗)`, or `χ'(𝓗) ≤ n`.
* `HugeStep2.lean`    — **LEMMA 7.3 (`huge-edge-absorption-lemma`) IS PROVED**
                       as `huge_edge_absorption`: the partner choice
                       `huge_pair`, the two internal steps
                       `huge_internal_step_small`/`huge_internal_step_large`,
                       the defect choice `huge_pick_S`, the uniform one-step
                       lemmas `huge_step_cov`/`huge_step_defect`, the
                       iterations `huge_iter_cov`/`huge_iter_defect` and the
                       assembly.
* `RegReservoir.lean` — **LEMMA 11.2 (`lem:reg_reservoir`) IS PROVED**:
                       `exists_regularising_reservoir` produces, for an
                       `(ρ,ε)`-full `𝓗` and a `(ρ/2,ξ,ξ,ε)`-absorber `Rabs`,
                       a `(ρ,ξ,ε,Rabs,𝓥)`-regularising reservoir
                       `Rreg ⊆ E(G) ∖ Rabs`, from `GFactorStatement` and the
                       numeric margins.  The formalised proof follows the
                       paper: the clique `S ⊆ V^{(n-1)}(G)`
                       (`exists_clique_finset`), the reserved family `R'`
                       (`exists_reservoir_subfamily`), the induced graph
                       `G[W] - Rabs - R'`, the functions
                       `f = ⌊ρ d_G + ξn - d_Rabs - d_R'⌋` and `g = f - 1`
                       (`fval`), the verification of the Lovász condition in
                       its two cases (`lovasz_condition`), and the final
                       `(R1)`/`(R2)` degree estimates (`reg_R1_arith`,
                       `reg_R2_up_arith`, `reg_R2_W0_arith`).
* `LowerReg.lean`     — **PROPOSITION 10.3 (`obs:del_lowerreg`) IS
                       PROVED**: the robustness of lower regularity, both
                       under deleting a subgraph of maximum degree `≤ αn`
                       (`lowerRegular_of_delete`, via the fibre counting
                       `edgeCount_eq_sum_fiber` + `fibreCount_le_degAt` and
                       the subadditivity `edgeCount_union_le`) and under
                       passing to a slightly larger vertex set
                       (`selfLowerRegular_mono`, for the self-regularity
                       predicate `SelfLowerRegular`).
* `OptCol.lean`       — Theorem 10.8 (`thm:optcol`, Glock–Kühn–Osthus) as the
                       deep input `GKOStatement`, **in the faithful
                       existential-threshold form** of the paper (its body is
                       verbatim that of `Work.Deep.GKO.GKOStatementFixed`, so
                       the two `Prop`s are definitionally equal; the old
                       linear-hierarchy form is retained as
                       `GKOStatementLinear`), and **Corollary 10.13
                       (`cor:optcol`) in the even case**
                       (`optcol_corollary_even`).  Also provides
                       `hypergraphMaxDegree_eq_sup`, `degAt_le_maxDegree`,
                       `edgeCount_comm`, `edgeCount_le_sum_degAt_left`,
                       `maxDegree_le_sum_sub` and
                       `maxDegree_ge_of_selfLowerRegular` (`Δ ≥ (p-3ε)n`),
                       plus the *core* form `optcol_corollary_core` (which
                       takes the paper's `(def_ineq₂)` at a minimum-degree
                       vertex rather than the "`≥ Δ` vertices of degree
                       `< Δ`" hypothesis).
* `OptColOdd.lean`    — **§10 COMPLETE: the odd case of Corollary 10.13**
                       (`optcol_corollary_odd`).  The parity-free
                       *faithful* `optcol_corollary` lives in
                       `OptColFaithful.lean` (it needs the `GKO` chapter,
                       which lies downstream of this file).  Implements the
                       paper's reduction
                       for odd `n`: `famImage` (image of a hypergraph under an
                       injective vertex map), `extendVertex` (add a new vertex
                       `Fin.last n` joined to a set `T`), the degree/
                       max-degree bookkeeping (`degAt_extendVertex_castSucc`,
                       `degAt_extendVertex_last`,
                       `hypergraphMaxDegree_extendVertex`,
                       `degAt_extendVertex_le_max`), the edge-count transport
                       (`castSuccFinset`, `edgeCount_famImage_castSucc`) and
                       the lower-regularity transport
                       (`selfLowerRegular_famImage_castSucc`,
                       `selfLowerRegular_extendVertex`, i.e. LR2 with
                       `α = 1/2`), then applies `optcol_corollary_core` to
                       the extended graph on `Fin (n+1)`.
* **New commons lemma** (proved by the fleet, verified importable here):
                       `Commons.Combinatorics.Matching.upper_regular_exists_injective`
                       — Proposition `crossing-matching-prop` of §7: an upper
                       `(ρ,ξ)`-regular bipartite-like relation in which every
                       left vertex has degree `≥ 2ρ|A|` and `ξ v(H) ≤ ρ|A|`
                       has a matching covering the left side (Hall).
* `Obs12.lean`        — `claim:easyobs` (EP1): every edge of `𝓗` meeting
                       `U = V_+^{(1-ε)}(G)` has size at most `εn`
                       (`edgeSize_le_of_meets_Vplus`).
* `Absorption.lean`   — §7 (vertex absorption) foundations:
                       `absorberFam R U` (the paper's `𝓕(R)`),
                       `PseudoRandom` (Definition
                       `pseudorandom-matching-def`),
                       `AbsorbableByPseudo`/`AbsorbableBySmall`/
                       `AbsorbableByTypical`/`Absorbable` (Definition
                       `def:absorbable`), the matching API
                       (`mem_matchVert`, `matchVert_mono`,
                       `subset_matchVert`, `matchVert_union`,
                       `isMatching_union`), and the two matching
                       propositions of the section:
                       `exists_matching_covering_of_upperRegular`
                       (Proposition `crossing-matching-prop`, in the
                       `A`/`VN` form used by the absorption lemma, built on
                       the commons lemma
                       `Commons.Combinatorics.Matching.upper_regular_exists_injective`)
                       and `exists_matching_covering_of_greedy` (the
                       greedy/Hall counterpart, used when `|A|` is small).
* `CrossingAbsorption.lean` — §7.1, **Lemma
                       `crossing-absorption-lemma` IS PROVED** (the case
                       `|U| ≤ n/100`): `crossing_absorption` extends `k ≤ κn`
                       edge-disjoint matchings, each `(γ,κ)`-pseudorandom
                       w.r.t. `𝓕(R) ∪ {U}`, by matchings of `R` so that the
                       result has perfect coverage of `U`.  Built from
                       `crossing_step` (one-step absorption, itself from the
                       degree estimate `crossing_degree`/`crossing_degree_chain`
                       and the two matching propositions) and the iteration
                       `crossing_iter`.  The numeric margins live in
                       `CrossingMargins` (`crossing_arith_main`,
                       `crossing_arith_greedy`).  The remaining §7 lemmas
                       (`internal-absorption-lemma`,
                       `huge-edge-absorption-lemma`,
                       `difficult-edge-absorption`) are the next layer.
* `Reservoir.lean`    — the definitions of the paper used by §7–§12:
                       `𝓗^{(i)}` (`Hypergraph.powFam`), the 2-graph
                       `G = 𝓗^{(2)}` (`Hypergraph.pow2`), the neighbourhood
                       `nbrs R v` and degree `degAt R v`, the vertex sets
                       `Vplus`/`VgeNat`/`VeqNat` (`V_+^{(x)}`, `V_+^{(m)}`,
                       `V^{(d)}`), matchings and coverage (`matchVert`,
                       `Covers`, `PerfectCoverage`, `NearlyPerfectCoverage`),
                       the quasirandomness vocabulary of Definition 7.1
                       (`Typical`, `UpperRegular`, `LowerRegular`) and
                       Definition 7.3's absorbers (`IsAbsorber`,
                       `incidentTwo`), Definitions 11.1–11.2's reservoirs
                       (`IsPseudoReservoir`, `IsRegularising`), and the
                       `(ρ,ε)`-full condition and Type-A/Type-B colourings of
                       §12 (`IsFull`, `IsTypeA`, `IsTypeB`, `medLarge`).
* `AbsorberDeletion.lean` — **Observation `obs:del_absorber`**: increasing `γ`
                       preserves `(ρ,γ,ξ,ε)`-absorbers
                       (`IsAbsorber.mono_gamma`), and deleting from an
                       absorber a subfamily of maximum degree at most `αn`
                       leaves a `(ρ,γ+α,ξ,ε)`-absorber (`IsAbsorber.delete`),
                       with the auxiliary `nbrs_eq_union_sdiff`.  This is the
                       observation used in Steps 4--6 of §12.
* `S12Setup.lean`    — **§12, Step 3 IS PROVED** (`exists_S12Colours_typeA`,
                       `exists_S12Colours_typeB`): from a Type-A (resp. Type-B)
                       colouring `φ` of the medium and large edges of `𝓗`
                       one builds the colour sets `C_med`, `C_diff`, `C_huge`,
                       `C_large`, `C_main`, `C_buff`, `C_final` of the final
                       assembly, together with the parameters
                       `D = ⌊(1-ρ)(n-1)⌋`, `D' = ⌊10γ^{1/2}D⌋`, and proves the
                       observations **(T1)** (`φ⁻¹(c) = ∅` for
                       `c ∈ C_buff ∪ C_final` in the Type A case) and **(T2)**
                       (`φ⁻¹(c) ⊆ 𝓗_large ∖ 𝓗_huge` in the Type B case) and
                       the size bound `|C_final| ≥ (ρ - 15γ^{1/2})n`
                       (`eqn:bound_prev_colours`).  The pieces:
                       `IsDifficultSet` (the vertex-set form of
                       `Definition defn:difficult`), the colour sets
                       `hugeColourSet`/`largeColourSet`/`diffColourSet`,
                       `card_hugeColourSet_le` (`|φ(𝓗_huge)| ≤ e(𝓗_huge)`),
                       `card_diffColourSet_le_one_of_typeA`/`..._of_typeB`
                       (Claim 12.1 (EP4)/(EP3)), and the generic finset facts
                       `exists_subset_card_max_inter` /
                       `subset_of_subset_card_max_inter` (the maximising
                       subset `C_main` contains `C_large` whenever
                       `|C_large| ≤ D`).
* `S12Step4.lean` / `S12Step5.lean` / `S12Step8.lean` — **§12, Steps 4, 5 and
                       (the structural part of) Step 8 ARE PROVED**.
                       Step 4 (`step:diff`): applying Lemma 7.12
                       (`difficult_edge_absorption`) to the (at most one)
                       difficult colour class either colours `𝓗` with `n`
                       colours or produces the matchings `𝓜_diff`, the
                       truncated absorber `R₁ = R_abs ∖ ⋃𝓜_diff`
                       (`(eq:R1abs)`: `R₁` is a `(ρ_abs, 3γ/2, ξ, ε)`-absorber,
                       via the robustness observation `obs:del_absorber`) and
                       the defect set `S₁ = S ∖ ⋃(V^{(n-2)} ∖ V(M_c))`
                       (`(eq:boundS1)`: `|S₁| ≥ |S| - 5`).  Step 5
                       (`step:step5`): applying Lemma 7.3
                       (`huge_edge_absorption` with `3γ/2` for `γ`) to the
                       huge and medium colour classes gives the matchings
                       `𝓜_hm` (HM1/HM2); the absorbability of the colour
                       classes is verified inside from the absorber `R₁`, the
                       collection `𝓥` of `(def:cv)` and the size bounds of
                       Step 3.  Step 8 (`eqn:h_final`): the decomposition
                       `𝓗 = ⋃𝓜_prev ∪ (R_res ∖ ⋃𝓜_prev) ∪ ⋃_{c∈C_final}φ⁻¹(c)`.
                       These modules provide `colourFam φ c` (a colour class
                       as a family of edges of `𝓗`), `subFam`, the
                       enumeration `colourEnum` of a colour set, and the
                       absorber-deletion lemmas.
* `Nibble.lean`       — **the deep inputs of §8/§9 recorded as `Prop`s** (in
                       the style of `KahnStatement`/`EGJStatement`):
                       `NibbleStatement` (Lemma `lem:nibble2`, the Nibble
                       Lemma) and `LeftoverStatement` (Lemma `lem:leftover`),
                       together with the multi-hypergraph matching vocabulary
                       they need (`MultiHypergraph.edgeSet`, `IsMatching`,
                       `pow2`, the families `nonsing`/`toFam`/`famOf` and their
                       matching/coverage lemmas, `EdgeDisjointFam`).  Neither
                       statement is proved: the paper derives `lem:nibble2`
                       from `SparseEGJStatement`/`EGJStatement` plus `lem:embed`
                       and `lem:pseudorandom_matching`.
* `S12Step6.lean`    — **§12, Step 6 (`step:step6`) IS PROVED**
                       (`s12_step6`, concluding `S12Step6Result`): the Nibble
                       Lemma applied to the colour set `C_main`.  From the
                       regularising lemma (`𝓗'` with
                       `𝓗'.edges = 𝓗_small ∖ R_res` and
                       `d_{𝓗'}(w) = (1-ρ)(n-1) ± βn/2`) and
                       `𝓗* = 𝓗' ∖ ⋃𝓜_diff` (degrees `(1 ± 2β)D`) the module
                       verifies conditions C1--C4 of `NibbleStatement` --
                       C4 needs the estimates `card_cmain_meeting_le` (Claim
                       12.1 (EP2) for the colours of `C_main`) and
                       `IsS12Colours.classVertexCount_le_of_mem_cmain` -- and
                       obtains edge-disjoint matchings `N_c ⊇ φ⁻¹(c)` with
                       N1--N3.  Deleting the singleton edges gives the
                       matchings `𝓜_main` of `𝓗` (MA1: `M_c ⊇ φ⁻¹(c)` and
                       `M_c ∖ φ⁻¹(c) ⊆ (𝓗_small ∖ (R_res ∪ ⋃𝓜_diff)) ∪ R₂`,
                       MA2: `|E_{R_abs}(w) ∩ ⋃M_c| ≤ 2γD` and
                       `Δ(𝓗_rem) ≤ 2γD`), the absorber
                       `R₃ = R₂ ∖ ⋃_c N_c` is a `(ρ_abs, 4γ, ξ, ε)`-absorber
                       (`(eq:R3abs)`) and `S₃ = S₂ ∖ ⋃_c (U ∖ V(N_c))` satisfies
                       `(eq:boundS3)` (`|S₃| ≥ 4εn` when `|U| > (1-10ε)n`).
* `S12Step6Aux.lean`  — the self-contained estimates needed to check the
                       hypotheses of the Nibble Lemma in §12 Step 6:
                       `Dparam_floor_bound` (`|(1-ρ)(n-1) - D| ≤ 1` for
                       `D = ⌊(1-ρ)(n-1)⌋`), `s12_star_degree` (the C3 degree
                       condition `d_{𝓗*}(w) = (1 ± 2β)D` for
                       `𝓗* = 𝓗' ∖ ⋃𝓜_diff`, from the regularising lemma and
                       `MultiHypergraph.abs_deg_sdiff_sub_le`),
                       `s12_C1_slack` (`D + γn ≤ |S₂|` from `D + 4εn ≤ |S₂|`)
                       and `s12_C4_small` (`|V(M_c)| ≤ βn ≤ 2βD`).
* `S12Step7.lean`    — **§12, Step 7 (`step:step7`) IS PROVED** (`s12_step7`,
                       concluding `S12Step7Result`): the Leftover Lemma
                       (`LeftoverStatement`) applied to the colour set
                       `C_buff` and the leftover hypergraph
                       `𝓗_rem = 𝓗_small ∖ (R_res ∪ ⋃𝓜_diff ∪ ⋃M_c)`.  The
                       module verifies L1--L5 (the estimates
                       `card_colours_meeting_le` -- Claim 12.1 (EP2) for an
                       arbitrary set of large colours -- for L4, the
                       monotonicity `IsAbsorber.mono_set`/`mono_gamma` for
                       L3, and the vertex-set bounds of T2 for L2) and obtains
                       the matchings `𝓜_buff` with (B1)
                       `M_c ⊇ φ⁻¹(c)`, `𝓗_rem ⊆ ⋃_c (M_c ∖ φ⁻¹(c)) ⊆ 𝓗_rem ∪ R₃`
                       and (B2) the perfect/nearly-perfect coverage of `U`
                       with defects in `S₃`.
* `S12Step9.lean`    — **§12, Step 9 (`step:step9`), the counting part IS
                       PROVED**.  With `m(w) = |{c : w ∉ V(M_c)}|` the number of
                       matchings of `𝓜_prev^*` missing `w`, the theorem
                       `s12_mbound` derives `(eqn:mbound_1)`--`(eqn:mbound_3)`
                       (`m(u) ≤ 1` on `U ∖ S₁` and `m(v) = 0` on
                       `V^{(n-1)} ∖ S₁`; `m(u) ≤ 2` on `U ∖ V^{(n-2)}` and
                       `m(v) ≤ 1` on `V^{(n-2)}`; and `m(u) ≤ 1` on
                       `U ∖ V^{(n-1)}`, `m(v) = 0` on `V^{(n-1)}` when
                       `|U| ≤ (1-10ε)n`) from the covering properties of
                       `𝓜_diff` and `𝓜_rest`; and `s12_uc` derives the degree
                       bounds UC2--UC4 from `(eqn:deg_h_final)`
                       (`s12_deg_h_final`) plus these `m(w)`-bounds.
* `S12Step8r.lean`   — **§12, Step 8, the rest of `stat:r_rem` IS PROVED**:
                       the equilibrium analysis of `G_final`.  `s12_deficit`
                       is `(eqn:deficit)` (`d_{R_res ∖ R_final}(w) ≤ |t| + C`,
                       from MA2(i) and the sizes of `𝓜_diff ∪ 𝓜_hm ∪ 𝓜_buff`);
                       `s12_delta_le` turns the Type A₂ reservoir bounds and
                       `(eqn:deficit)` into `Δ(G_final) - d_{G_final}(v) ≤ 22εn`
                       for every `v` (the form consumed by `optcol_corollary`);
                       and the lower-regularity half uses the counting lemmas
                       `edgeCount_induce`, `fibreCount_ge_real`,
                       `edgeCount_ge_of_deg` and `edgeCount_incidentTwo_ge`
                       (`e_{G'}(A,B) ≥ (|A| - εn)|B|` on `U`), the robustness
                       `lowerRegular_of_delete` (Prop 10.3.1) and
                       `SelfLowerRegular.mono` to give
                       `s12_selfLowerRegular_U` (the induced family on `U` is
                       lower `(ρ/3, η)`-regular) and `s12_lowerRegular_final`
                       (`G_final` is lower `(ρ/4, ε^{1/3})`-regular).
* `S12Mprev.lean`    — **the assembly of `𝓜_prev`** (the family of matchings
                       built in Steps 4--7), part 1: the structural glue.
                       `prevFam` is the family of vertex sets of `𝓜_prev^*`
                       (the colour `c` carrying the matching of the step whose
                       colour set contains `c`); the module proves that it is
                       supported on `C_prev` (`prevFam_eq_empty`), that each
                       member is a matching of `𝓗_reg` (and of `𝓗` after
                       deleting singletons), that the coverage at a colour
                       transfers from the branch containing it
                       (`sdiff_famVert_prevFam_subset`,
                       `sdiff_famVert_prevFam_subset_S1`), and that "covered"
                       means the same in `𝓜` and in `𝓗` at the vertices of `U`
                       (`matchVert_toFam_of_mem_famVert`, via the absence of
                       singleton edges of `𝓗_reg` at `U`).  It also defines the
                       defect sets `S₁`, `S₂`, `S₃` of Steps 4--7 and proves
                       **`ncard_miss_le_one`**: at most one matching of
                       `𝓜_hm ∪ 𝓜_main ∪ 𝓜_buff` misses a given vertex of `U`
                       (the hypothesis `hnp` of `s12_mbound`), which is where
                       the nesting `S₃ ⊆ S₂ ⊆ S₁` is used.  Finally
                       `prevFam_subset_hyp`/`ncard_single_miss_eq_zero` show
                       that the singleton bookkeeping `hsingle` of
                       `s12_deg_h_final` is *vacuous* for `𝓜_prev` (all four
                       steps produce matchings of `𝓗`, not of `𝓗_reg`), that
                       `hfinOf` is `𝓗_final = 𝓗 ∖ ⋃𝓜_prev` with the index type
                       `↥C_prev`, and `card_Cprev_sub` is the counting
                       hypothesis `|C_prev| = n - |C_final|` of
                       `s12_deg_h_final`.  The instantiation is begun with the
                       ambient vertex-set data: `hdeg_le_pred` (`d_𝓗(v) ≤ n-1`),
                       `two_mul_hdeg_sub_le_degAt` (the paper's
                       `eqn:non-graph-degree`), the inclusions
                       `Vdeg_pred_subset_Vplus`/`Vdeg_pred2_subset_Vplus`/
                       `Vdeg_plus_subset_Vplus` (`V^{(n-1)}(𝓗) ⊆ U` and
                       `V_+^{(n-2)}(𝓗) ⊆ U`), the characterisations
                       `mem_Vdeg_pred_iff`/`mem_Vdeg_plus_iff` (the `hVn1`/`hVn2`
                       hypotheses of `s12_uc`, `Vn1set`/`Vn2set` being the sets
                       `Vn1`/`Vn2`).
* `S12Step10.lean`   — **§12 Step 10, the final colouring** (the last step):
                       the output of the step is packaged as the structure
                       `S12Finishing` (a family `Mfin` of matchings of `𝓗`,
                       supported on `C_final`, extending the colour classes of
                       `φ` on `C_final` and covering the reserved leftover
                       graph `R_final`).
                       * the two graph cases A₁/A₂ share the theorem
                       `exists_finishing_of_colorable`: a colouring of the
                       leftover 2-graph `R` with `|C_final|` colours, together
                       with the vanishing of the colour classes `φ⁻¹(c)` on
                       `C_final` (the paper's (T1)), produces `S12Finishing`;
                       `exists_finishing_vizing` is the immediate corollary in
                       the "Vizing pair-family" form produced by
                       `Commons.Combinatorics.SimpleGraph.edgeColoring_of_pairFamily`.
                       * Case B (Type B, the FPP-extremal case) is
                       `exists_finishing_hall`: the Hall-based finishing
                       valuation `ψ : R → C_final` avoiding, at both ends of
                       every edge, the colours already used by `φ` there
                       (the paper's `C_w`, here `finalColoursAt φ Cfin w`)
                       makes `ψ⁻¹(c) ∪ φ⁻¹(c)` a matching and yields
                       `S12Finishing`; `exists_finishing_hall_of_margins`
                       derives the Hall hypotheses of Lemma 10.2 from the
                       paper's numerical data (`7δn ≤ |C_final|`, `|U| ≤ δn`,
                       every edge of `R_final` meeting `U`, the degree
                       deficiencies `d_{R_final}(w) ≤ |C_final| - 1 - |C_w|`
                       and the two smallness conditions on `C_w`), using the
                       ported commons lemma
                       `Commons.Combinatorics.SimpleGraph.hallFinishing_of_pairFamily`.
                       * the final packaging is `chromaticIndex_le_of_decomposition`
                       (𝓜_prev together with 𝓜_final on the disjoint colour
                       sets `C_prev`, `C_final` gives `χ'(𝓗) ≤ n` via
                       `chromaticIndex_le_of_matchingDecomposition`) and
                       `chromaticIndex_le_of_prev_and_finishing` (the same,
                       with the covering hypothesis in the paper's form:
                       every edge lies in `𝓜_prev`, in `R_final` or in a
                       colour class of `C_final`).
                       Auxiliary: `nbrs_eq_pair_offdiag`,
                       `degAt_eq_pair_offdiag` (the `degAt` form of the
                       Vizing degree hypotheses) and
                       `colorable_of_pairFamily_coloring`.
* `S12Inst5.lean`    — **§12 Step 5, instantiated and packaged.**
                       `s12_step5_inst` discharges all the hypotheses of
                       `s12_step5` (the `𝓥` of `(def:cv)`, `B = 0` with
                       `internalMatchingInput`, the degree hypothesis at `U`
                       from `U = V_+^{(1-ε)}(G)`, and the size/absorbability
                       data of the huge and medium colour classes from
                       `IsS12Colours`): `(eqn:size_hm)`
                       (`card_chuge_union_cmed_le`, `|C_huge ∪ C_med| ≤ 3γn/2`
                       from `natCard_hugeEdges_le`), the `(def:cv)`
                       memberships, `|V(φ⁻¹(c)) ∩ U| ≤ εn`
                       (`huge_class_inter_U_le` + `SingletonClassesForHuge`),
                       `|V(φ⁻¹(c))| ≤ 3γn/2` for medium colours, the
                       non-difficulty of huge colours (`hCdiff_full`), and the
                       avoidance of `R₁` (colour classes consist of edges of
                       size `> r₁ ≥ 2`).  The structure `IsS12Step5` records
                       the output (HM1, HM2, `(eq:R2abs)`, `(eq:boundS2)`), and
                       `s12_step5_pack` produces it from the Step-4 output: the
                       truncated absorber `R₂ = R₁ ∖ ⋃𝓜_hm` is shown to be a
                       `(ρ_abs, 2γ, ξ)`-absorber via `IsAbsorber.delete`
                       (`Δ(R₁ ∖ R₂) ≤ |C_huge ∪ C_med|` by
                       `hdeg_famUnionFinset_le_card`) and the sharper `(10ξ)`
                       absorbability of `R₁` (the paper's `ξ ≪ γ`), and the
                       defect set `S₂ = S₁ ∖ ⋃_c (U ∖ V(M_c))` loses at most
                       `|C_huge ∪ C_med|` vertices (giving `(eq:boundS2)`).
                       Auxiliary: `hdeg_famUnionFinset_le_card` (the union of
                       `|C|` matchings has degree at most `|C|` at every
                       vertex).
* `S12Step9Pack.lean` — **§12 Step 9, packaged: the `m(w)`-bounds for
                       `𝓜_prev`.**  `prevFamFull` is the family `𝓜_prev^*` of
                       `S12Mprev.lean` (`prevFam`) extended by the whole vertex
                       set outside `C_prev`, so that it is a family indexed by
                       all of `Fin n` whose matchings miss *nothing* off
                       `C_prev`; `prevMiss ... w` is the set of colours of
                       `𝓜_prev` whose matching misses `w` (so that the counts
                       of `s12_mbound` and `s12_deg_h_final` line up).
                       `s12_step9_mbound` instantiates `s12_mbound` with this
                       family: `ιdiff` is `C_diff`, and the hypotheses
                       `hdiff1`, `hdiffVn1`, `hdiffVn2`, `hrestcov`, `hnp`,
                       `hperf` are discharged from the Step-4/5/6/7 data using
                       `sdiff_famVert_prevFam_subset`, `ncard_miss_le_one`
                       (the `Finset.filter` counts of `S12Mprev.lean`), and
                       the branch descriptions of `prevFam`
                       (`famVert_prevFam_eq_Cdiff`/`_Cmain`/`_Cbuff`/`_HM`).
                       Auxiliary membership lemmas: `mem_of_mem_prev_notMem_Cdiff`,
                       `mem_med_huge_of_mem_prev`, `mem_prev_of_mem_Cmed` etc.
* `S12Assem.lean`     — **the §12 assembly** (in progress).  Contains:
                       * `isTypeA_exists_of_nonExtremal`/`isTypeB_exists_of_extremal`:
                         the passage from Theorem 6.7's alternatives (colourings
                         of all of `𝓗`) to the §12 hypotheses `IsTypeA`/
                         `IsTypeB` (colourings of `𝓗_med ∪ 𝓗_large`), together
                         with the restriction lemmas for colourings
                         (`SingletonClassesForHuge_restrict`, ...);
                       * `S12Margins`: the numerical hypotheses of the assembly
                         (`1/n ≪ ξ ≪ 1/r₁ ≪ β ≪ κ ≪ γ ≪ ε ≪ ρ ≪ 1`);
                       * `s12_step5_pack_gen`: §12 Step 5 with the huge/medium
                         size bounds supplied directly (so that it is available
                         in Types A and B alike);
                       * `s12_steps67`: §12 Steps 6 and 7 (the nibble and the
                         leftover) from the Step-4/5 data;
                       * `S12Out`: the output of Steps 8/9 (the family `𝓜_prev`,
                         `R_final`, `𝓗_final`, `(eqn:h_final)`,
                         `(eqn:deficit)`, `degAt R_final w + |C_w| = d_{𝓗_final}(w)`
                         and `UC1`--`UC4` + the count of `|C_final|` vertices of
                         degree `< |C_final|`);
                       * `isS12Step4_of_Cdiff_empty`: Step 4 in Type B;
                       * `hdeg_famUnionFinset_colourFam`: the degree of the union
                         of colour classes is the number of colours present at a
                         vertex;
                       * `prevFam_pairwise_disjoint`: the pairwise
                         edge-disjointness of the four families of `𝓜_prev`
                         (the hypothesis `hdisj` of `s12_deg_h_final`).
* `S12Finish.lean`    — **§12 Step 10, the three finishers.**  Each consumes
                       the Step-8/9 output `S12Out` and the type-specific data
                       and produces `χ'(𝓗) ≤ n`:
                       * `degAt_R_final_of_T1`: in Type A the colour classes
                         of `C_final` are empty, so
                         `d_{G_final}(w) = d_{𝓗_final}(w)`;
                       * `s12_finish_A1` (Type A₁): `Δ(R_final) ≤ |C_final| - 1`
                         from `UC1`/`UC2`/`UC4`, then Vizing
                         (`exists_finishing_vizing_of_degAt`);
                       * `s12_finish_A2` (Type A₂): either Vizing, or
                         `Δ(R_final) = |C_final|` and Corollary 10.13
                         (`GKOStatement`, instantiated at the given `n` as the
                         hypothesis `hcor`) gives the colouring;
                       * `s12_finish_B` (Type B): the Hall-based finishing
                         (`exists_finishing_hall_of_margins`).
* `S12Core.lean`      — **the core of the §12 assembly (Steps 8 and 9),
                       COMPLETE.**  From the Step-1--Step-5 data (the colour
                       sets, the reservoir/absorber, `𝓜_diff`, `𝓜_hm`), the
                       nibble (`s12_step6`) and the leftover lemma
                       (`s12_step7`), `s12_core` produces `𝓜_prev`,
                       `R_final = R_res ∖ ⋃𝓜_prev` and
                       `𝓗_final = 𝓗 ∖ ⋃𝓜_prev` together with every field of the
                       structure `S12Out`: the decomposition `(eqn:h_final)`,
                       the deficit bound `(eqn:deficit)`, the degree identity
                       `(eqn:deg_h_final)`, the bounds `UC1`--`UC4` and the
                       count of the `|C_final|` vertices of smaller degree.
                       The paper's `m(w)` counts the misses of the *starred*
                       family `𝓜_prev^*` (the `C_main` matchings keeping their
                       singleton edges), here `Mstar`; the singleton
                       bookkeeping `hsingle` of `s12_deg_h_final` is supplied
                       by the faithful form of NB1 recorded in
                       `NibbleStatement` and by `h6₂₃` of `S12Step6Result`.
* `S12Numeric.lean`   — the numerical plumbing of the §12 assembly: the
                       derivations of the numeric hypotheses of
                       `s12_step4`--`s12_step7`/`s12_mbound`/`s12_uc` from the
                       paper's hierarchy and the definitions of `D`/`D'`
                       (`Dparam_ge_sub`, `n_le_two_Dparam`,
                       `two_thirds_beta_le`, `EP2num_le`,
                       `overlap_le_gamma_mul`, `D'param_ge_half`,
                       `four_gamma_le_sqrt`).
* `MainThm2.lean`     — **Theorem 1.2 of the paper (`main-thm-2`) IS
                       PROVED** from the deep inputs Molloy–Reed and Kahn
                       (`mainThm2_of_deep`): for every `δ > 0` there are `n₀, σ > 0`
                       such that every `n`-vertex linear `𝓗` (`n ≥ n₀`) with
                       `Δ(𝓗) ≤ (1-δ)n` and at most `(1-3δ)n` edges of size
                       `(1±δ)√n` is `(1-σ)n`-colourable.  The pieces:
                       * **step 1** (`volume_exEdges_lt_of`,
                         `volume_exEdges_lt`, `exvol_arith_local`, via
                         `volume_le_canon_card_mul_real`): the volume of the
                         FPP-extremal edges is `< 1-δ` (the `⌈(1+δ)√n⌉`
                         rounding trap is avoided by using the *real* bound);
                       * **the hierarchy**: `δ₂ = min δ (1/4) δ₀` from
                         Theorem 6.1, then `σ = min σ₀ (δ₂/64)`,
                         `γ₁ = min γ₁₀ (σ/4)`, `β = min β₀ (γ₁/4)`,
                         `r₁ = max R₁ 2`, `r₀ = max R₀ (max (r₁+1)
                         (⌈4r₁/β⌉+2))`, `α = 8(γ₁+β)`,
                         `K = ⌊(1-σ)n⌋`, `n₀ = max N₀ (…⌈1000/δ₂²⌉…⌈2/δ⌉…
                         ⌈D₀/(1-δ)⌉…)`;
                       * **Theorem 6.1** applied to `medLarge 𝓗 r₁`, with the
                         *extremal* alternative ruled out by step 1
                         (`not_largeEdgeExtremal_of_volume`);
                       * **relabelling** (`colourCast`, `Coloring.relabel`,
                         `Coloring.colorClass_relabel`) into `Fin K`;
                       * **Kahn** on the small edges with the lists
                         `smallLists` = (colours of the large edges meeting
                         `e`) ∪ (`Cmed` image); the list size is
                         `≤ r₁n/(r₀−1) + γ₁n ≤ α(1-δ)n/2` (this is where
                         `α = 8(γ₁+β)` — rather than the paper's `α = 3β` —
                         is needed, since `γ₁ ≫ β` in the hierarchy);
                       * **gluing** (`colorable_of_mediumLarge_colouring`,
                         via `coloringUnionCrossGen`): the two colourings
                         combine on the cover
                         `𝓗_small ∪ (𝓗_med ∪ 𝓗_large)`, because a small
                         edge never meets a medium/large edge in a colour of
                         its list.  The reusable pieces are
                         `card_mediumLarge_meeting_le`,
                         `card_largeColours_le` (the crossing count and its
                         real ratio bound `r₁/(r₀−1) ≤ β/4`), and the
                         numeric lemmas `alpha_le_five_halves`,
                         `one_add_alpha_mul_le`, `kahn_bound_of_floor`,
                         `ratio_le_of_r₀`.
* **New commons lemmas** (proved by the fleet, verified importable here):
                       `Commons.Probability.Chernoff.chernoff_two_sided_finite`
                       (the two-sided Chernoff bound on a finite product
                       space, `∑_s ∏_i w_i(s_i)·1{t ≤ |∑ X_i s_i − μ|} ≤
                       2exp(−t²/(2(μ+t/3)))` for weights `≤ 1` — **NOTE**:
                       this module and the commons
                       `…chernoff_two_sided_finite_weighted` both declare
                       `Commons.Probability.Chernoff.upper_tail`, so only
                       *one* of them may be imported into the cone; we import
                       the weighted one transitively through
                       `exists_finset_sum_close`),
                       `Commons.Data.Real.exvol_arith` (the volume
                       arithmetic of Theorem 1.2's step 1, used in
                       `MainThm2.volume_exEdges_lt`), and
                       `Commons.Combinatorics.FiniteSampling.exists_finset_sum_close`
                       (`|(R ∩ A_i).card − p·|A_i|| ≤ t_i` for some `R`
                       whenever the sum of the Chernoff failure bounds is
                       `< 1` — the probabilistic-method engine for §11's
                       Proposition 11.1).
* `Commons.Combinatorics.SimpleGraph.vizing_two_max` — **the refinement of
                       Vizing's theorem** used by Lemma 7.12: if at most two
                       vertices of `G` have degree `D` then
                       `G.lineGraph.Colorable D`.  (Proved by the fleet, in
                       the cone.)
* `Commons.Combinatorics.SimpleGraph.hall_based_finishing` — **the paper's
                       `hall-based-finishing-lemma` (Lemma 10.2)** as a
                       minimal-import commons lemma, in the cone: a graph all
                       of whose edges touch a small set `U`, with small
                       colour lists and small colour-degrees, has a proper
                       list edge-colouring (the finishing step of the
                       FPP-extremal regime in §12).
* `InternalAbsorption.lean`, `InternalStep.lean`, `InternalStepB.lean`,
                       `InternalMain.lean` — §7.2, **Lemma
                       `internal-absorption-lemma` IS PROVED**
                       (`internal_absorption`): for `k ≤ κn` edge-disjoint
                       matchings `N_i`, each `(γ,κ)`-pseudorandom w.r.t.
                       `𝓕(R) ∪ {U,S}`, there are matchings `N'_i ⊇ N_i` with
                       `N'_i ∖ N_i ⊆ R`, pairwise edge-disjoint, with perfect
                       coverage of `U` if `|U| ≤ (1-2ε)n` and nearly-perfect
                       coverage with defects in `S` otherwise.  The pieces:
                       the perfect-matching input `InternalMatchingInput`
                       (Proposition `internal-matching-prop`), the degree
                       estimate `internal_degree_chain`, the shared matching
                       `internal_matching_of`, the defect-vertex choices
                       `internal_pick_A`/`internal_pick_B`, the two one-step
                       lemmas `internal_step_A2`/`internal_step_B2`, and the
                       iteration `internal_iter` (which keeps the accumulated
                       matchings `used` and the injected defect set `P`
                       distinct).  The hypothesis `InternalMatchingInput` (the
                       paper's Proposition `internal-matching-prop`) is
                       **discharged** in
                       `Submission/EFL/Comm/InternalMatchingConnect.lean`
                       (`internalMatchingInput`), by transporting the ported
                       commons lemma through the `SimpleGraph ↥W` of a 2-edge
                       family (`graphOf`, with `graphOf_degree` and
                       `upperRegular_graphOf`) and converting a perfect
                       matching back into a matching family via the involution
                       `f v = ` (the unique neighbour of `v`).
* `HugeAbsorption.lean` — the opening of §7.3: Definition `defn:difficult`
                       (`IsDifficult`: a matching covering `≥ 3/4` of
                       `V(𝓗) ∖ U`, with `|V(𝓗) ∖ U| ≥ 2`) and its two
                       consequences used by the crossing part of Lemma 7.3,
                       `card_inter_compl_le_of_not_difficult` and
                       `card_matchVert_le_of_not_difficult` (not difficult +
                       `AB-huge` ⟹ `|V(M)| ≤ (3/4+ε)n`).  The `AB-huge`
                       alternative of `Absorbable` (`AbsorbableByTypical`) was
                       corrected to the paper's form (it now records
                       `U ∪ V(M), U ∖ V(M) ∈ 𝓥` for the *same* `𝓥` as `AB1`,
                       and no longer contains the pseudorandomness conjunct).
* `LargeEdge.lean`    — Theorem 6.7 (`large-edge-thm`) of the paper, stated
                       precisely on the exact definitions: colour-class
                       coverage (`classVertexCount`, real bounds), the
                       non-extremal (`LargeEdgeNonExtremal`) and extremal
                       (`LargeEdgeExtremal`) alternatives, hypergraph
                       `volume`, the volume bound `volume_le_one_of_linear`
                       for linear hypergraphs, the per-instance theorem
                       `LargeEdgeInstance` and the hierarchy-level
                       `LargeEdgeThmStatement`; the proof decomposition is
                       documented in the module header.

* `S12AMain.lean` / `S12MainA.lean`, `S12ANum.lean`, `S12MainA2.lean` +
                       `S12A2Main.lean`, `S12BNum.lean`, `S12MainB.lean` and
                       `S12ChainGen.lean` — **§12, the whole assembly**: the
                       Type A₁ branch (`s12_branch_A1`, `s12_A1_main`), the
                       Type A₂ branch (`s12_branch_A2`, `s12_A2_main`, with the
                       Corollary 10.13 finishing), the Type B branch
                       (`s12_branch_B`, `s12_B_main`, with the Hall finishing
                       at parameter `2δ`), the Steps 5--9 chain in the generic
                       form `s12_to_S12Out_gen`, and all the numeric side
                       conditions (`S12ANum`, `S12BNum`).
* `Embed.lean` — **`EmbedStatement`**, the *regular case* of the embedding
                       lemma `lem:embed` (`efl.tex:535`) that is consumed by the
                       proof of `lem:pseudorandom_matching`: the uniformisation
                       of a linear multi-hypergraph by `r`-uniform edges with
                       all degrees in `[D-C, D]`, together with the bijection
                       `ψ : e* ↦ e* ∩ V(𝓗)` identifying the new edges meeting
                       `V(𝓗)` with the old edges counted with multiplicity.
                       (This is *weaker* than the paper's lemma — it adds the
                       hypothesis `D - C ≤ d_𝓗(v)` at non-isolated `v`, which is
                       exactly the situation in which the lemma is used, and
                       without which the paper's `ψ` is not a bijection; see the
                       session note in `Roadmap.lean`.)
* `EmbedProof.lean` — the **first step of the proof of `lem:embed`**
                       (`exists_uniform_extension`): a linear hypergraph all of
                       whose edges have size in `[2, r]` can be made `r`-uniform
                       by adding `r - |e|` fresh vertices to each edge, without
                       changing the degrees at the old vertices.
* `S12Assembly.lean` — **the final assembly**
                       `eflStatement_of_deep : MolloyReedStatement →
                       KahnStatement → NibbleStatementFixed → GKOStatement →
                       eflStatement`, a one-line reference to
                       `Work.ConeSwitch.eflStatement_of_deep_faithful`
                       (`Submission/Work/ConeSwitch/Assembly.lean`), where the
                       whole endgame now lives: the constant hierarchy is
                       walked by hand, the Type-A₂ density `ρ` is chosen
                       *first* (then the thresholds of the faithful Corollary
                       10.13 are read off at `ρ/4`), the constants
                       `ε, γ, β, ξ, ζ, η, ηr, r₁, r₀` are produced *after* them
                       by `Work.ConeSwitch.exists_A2_params`, and the case
                       split on the *free* `IsFull 𝓗 ρ ε` dispatches to
                       `Work.S12Faithful.s12_branch_A2_faithful` or
                       `Work.ConeSwitch.s12_branch_A1_faithful` (both
                       parametric in `(ρ, ε)`); `eflStatement_of_bigEdges`
                       colours the singleton edges greedily at the end.

The *mathematical* proof of the theorem is the content of the Annals paper,
and **every step of its §§1--12 is now machine-checked** (sorry-free) in this
development, with the chain assembled end to end.  The **deep input `Prop`s**
of the paper that the assembly consumes are:

* `MolloyReedStatement` (Theorem 6.7's first tool) — **supplied** below by
  `Work.Deep.Sparse.molloyReedStatement`;
* `KahnStatement` (Theorem 6.7's second tool) — **supplied** below by
  `Work.Deep.Kahn.kahnStatement`;
* `NibbleStatementFixed` (`lem:nibble2`) — **supplied** below by
  `Work.Deep.Nibble.nibbleStatementFixed`.  The proved shape is the paper's
  asymptotic one (`Work.Deep.Nibble.MarginsConst` plus an existential `N₀`);
  the cone threads it through the pointwise form `NibblePointwise` above the
  threshold `nibbleThr` (`Submission/EFL/NibbleFixed.lean`), which each branch
  derives from its margin bundle (`marginsConst_of_bundle`) and its own
  enlarged threshold;
* `GKOStatement` (Theorem 10.8, via `optcol_corollary`, in the faithful
  existential-threshold form) — **the only remaining input**.

The nibble's parameter hierarchy `0 < 1/n₀ ≪ 1/r, ξ, β ≪ γ ≪ ε, ρ ≪ 1`,
`n ≥ n₀` and `D ∈ [n^{2/3}, n]` are recorded in the margin bundle
`NibbleMarginsStrong` (`Submission/EFL/Nibble.lean`), which the §12 chain
carries inside `S12Margins`; the strengthening `β ≤ γ₁⁴/10¹²` of the constant
`β` produced by `s12_step1` is what makes `β ≪ γ⁴ ≪ γ²ρε` — the separation the
proof of `lem:nibble2` actually uses, via the pseudorandom-matching lemma —
available in the Type A and Type B branches.

The paper's fifth input, `LeftoverStatement` (`lem:leftover`), has been
**eliminated**: `Submission/EFL/LeftoverLemma.lean` proves Lemma
`lem:leftover` from `KahnStatement` (and Lemma 7.3), so the §12 chain carries
the numerical bundle `LeftoverMargins` (proved for large `n` by
`exists_leftoverMargins`) instead of that input.

`NibbleStatement` is itself proved in the paper (from `SparseEGJStatement` +
`lem:embed` + `lem:pseudorandom_matching`), and formalising that reduction —
plus `lem:embed`, Kahn, Molloy--Reed, GKO and EGJ themselves — is exactly what
stands between this development and an unconditional `theorem_1_1`.
Concretely, once the last statement is supplied, `theorem_1_1` below is

    change eflStatement
    exact eflStatement_of_deep hMR hK hNib hGKO

(the statement of `theorem_1_1` is *literally* `eflStatement`).  Accordingly
`theorem_1_1` below is proved by `exact eflStatement_of_deep hMR hK hNib hGKO`,
the single remaining deep input `hGKO` being the only remaining `sorry`: this is
deliberate, so
that the whole machine-checked road (§S1--§12, the reordering lemma, Theorem
1.2, Lemma 11.3, Claim 12.1, the three branches of §12, the leftover lemma) is
*actually traversed* by the statement of the challenge theorem, and any
mismatch between `eflStatement` and `theorem_1_1` would be a compile error
rather than a compile-time no-op.
-/

/-- The statement of Theorem 1.1 (of the paper), in the `Submission` namespace
so that it is propositionally identical to the challenge statement. -/
theorem theorem_1_1 :
    ∀ᶠ n in atTop, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → 𝓗.chromaticIndex ≤ n := by
  -- The deep inputs of the paper.  `hMR`, `hK` and `hNib` are supplied by the
  -- `Work` chapters (`Work.Deep.Sparse`, `Work.Deep.Kahn`, `Work.Deep.Nibble`);
  -- `hGKO` is the single remaining input.  Everything else (the whole of
  -- §§1--12, the reordering lemma, Theorem 1.2, Lemma 11.3, Claim 12.1 and the
  -- leftover lemma `lem:leftover`) is proved in this development.
  have hMR : MolloyReedStatement := Work.Deep.Sparse.molloyReedStatement
  have hK : KahnStatement := Work.Deep.Kahn.kahnStatement
  have hNib : NibbleStatementFixed := Work.Deep.Nibble.nibbleStatementFixed
  have hGKO : GKOStatement := Work.Deep.GKO.OneFact.gkoStatement_elementary
  exact eflStatement_of_deep hMR hK hNib hGKO

end Submission
