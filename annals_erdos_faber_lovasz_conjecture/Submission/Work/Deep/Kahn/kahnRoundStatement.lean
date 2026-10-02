import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Nibble
import Submission.Work.Deep.Kahn.RoundDefs
import Submission.Work.Deep.Kahn.NibbleRoundDefs
import Submission.Work.Deep.Kahn.nibbleRegularised
import Submission.Work.Deep.Kahn.kahnEmbedding
import Submission.Work.Deep.Kahn.nibbleRoundGlue
import Submission.Work.Deep.Kahn.kahnCore_of_roundStepB
import Submission.Work.Deep.Kahn.kahnList_of_kahnCore
import Submission.Work.Deep.Kahn.kahnStatement_of_kahnList

/-!
# The one-round step of the nibble proof of Kahn's theorem

This module is the home of the target `Work.Deep.Kahn.kahnRoundStatement`
(of type `ErdosFaberLovaszConjecture.KahnRoundStatement`), and of the assembled deep input
`Work.Deep.Kahn.kahnStatement` (of type `ErdosFaberLovaszConjecture.KahnStatement`).

## What is proved here

`kahnRound_of_core : KahnCoreStatement → KahnRoundStatement`.

The one-round statement of `Nibble.lean` is *satisfied by the round that colours everything*:
taking `𝓗₀ := 𝓗` the progress clause reads `d_{𝓗∖𝓗}(v) = 0 ≤ (1-θ)·Δ(𝓗)` and the loss clause
is vacuous.  Hence `KahnRoundStatement` is *equivalent* (as a statement) to Kahn's theorem
`KahnCoreStatement` for hypergraphs with edges of size at least two.  The substance of the
subproject is therefore the proof of `KahnCoreStatement`.

## The remaining work (the deep input)

`KahnCoreStatement` is Kahn's theorem (Kang--Kelly--Kühn--Methuku--Osthus, Theorem 4.6;
Kahn, *Asymptotically good list-colourings*, JCTB 73 (1996)).  The proof is the semi-random
method ("Rödl nibble" with colours), in the form analysed in

  T. Kelly, D. Kühn, A. Methuku, D. Osthus, *A special case of Vu's conjecture: coloring
  nearly disjoint graphs of bounded maximum degree*, arXiv:2109.11438,

whose Theorem 2 (the "colour degree" theorem) implies Kahn's bound for linear hypergraphs
(their Corollary 3, via line graphs).  The development planned here runs the same argument
directly on hypergraphs, using the one-round procedure fixed in
`Submission/Work/Deep/Kahn/RoundDefs.lean`:

* **invariants of a state**: an edge-size bound `r`, a linearity hypothesis, a lower bound
  `λ ≤ |L e|` on the lists, an upper bound `D` on the *colour degrees*
  `D_x(γ) = #{e ∋ x : γ ∈ L e}` and an upper bound `Δ` on the vertex degrees;
* **one round** (activation class `0` of `K` uniformly, colour uniform in the list): the kept
  edges are properly coloured, the residual lists lose at most the colours of the activated
  edges meeting the edge (and none of the colours used by the kept edges — soundness), the
  expected loss is `λ - λ(1-p/λ)^{rD}`, the expected residual colour degree is at most
  `D((1-p)(1-p/λ)^{rD-1} + p(1-(1-p/λ)^{rD}))` and the expected residual degree at most
  `Δ(1 - p(1-p/λ)^{rD})`;
* **concentration** of these three quantities (deviation `D^{4/5}` with probability
  `exp(-D^{1/4})`), by a two-level Chernoff argument: condition on the "witness" coordinates,
  apply the Chernoff bound to the remaining independent indicators, and concentrate the
  conditional mean (itself a weighted sum of independent indicators) by another Chernoff
  bound; the exceptional outcomes (too many activated edges of one colour at one vertex) are
  handled explicitly;
* **the Lovász local lemma** over the bad events (one per edge, one per vertex and one per
  `(vertex, colour)` pair), which are mutually independent of all but `poly(D)` others, gives
  an outcome satisfying all three deviation bounds *simultaneously*;
* **iteration** of the round (the ratio `λ/D` improves by the factor `1 + Θ(p)` per round and
  hence reaches `8r` in `O(log r / p)` rounds) and the **finishing** step: with `λ ≥ 8rD` the
  residual colour degrees are so small relative to the lists that the residual hypergraph is
  list-colourable.

The two pieces above (the concentration analysis and the finishing step) are the remaining
content of this module.

## STATUS (and findings that matter for the continuation)

* `Work.Deep.Kahn.Round` (`RoundDefs.lean`) fixes the procedure and *proves* the combinatorial
  part: the kept edges form a proper colouring (`keptColoring`, `keptColoring_mem`) and the
  residual lists are sound (`not_mem_residual_of_kept`: a colour used by a kept edge at a vertex
  of `e` is removed from the list of `e`).
* `Work.Deep.Kahn.chernoff_uniform_prod` (proved) is the Chernoff bound on a uniform product
  space used for the *first level* of every deviation estimate here.
* `Work.Deep.Kahn.round_step` (`RoundStep.lean`, delegated) is the one-round step with the two
  deviation bounds (list sizes and residual colour degrees).
* **The progress must be measured by the colour degree, not by the vertex degree.**  The
  counterexample is a projective plane of order `q` with all lists equal: any two kept edges
  meet, so at most `(1+β)D` edges are kept per round, whereas a `p`-fraction per-vertex drop
  would require `Θ(nD/K)` kept edges.  Consequently the vertex-degree-based finishing
  (`listColorable_of_card_gt_sum_degree`) is *not* reachable by the iteration; the finishing
  must use the colour degree (as in KKMKO's use of Reed's *list-colouring constants* lemma:
  `|L(v)| ≥ 8·Δ(G,L)` implies list-colourability).
* The expectations of one round (with `λ = (1+β)D`, `p = 1/K`, `D_x(γ) ≤ D`, edge sizes ≤ r):
  * expected loss per edge: `λ(1 - (1-p/λ)^{rD})`, i.e. `|residual e| ≥ λ - prD`;
  * expected residual colour degree: `D((1-p)(1-p/λ)^{rD-1} + p(1-(1-p/λ)^{rD}))`; the
    *first-order* drop `(1-p/λ)^{rD}` is what makes the ratio `λ/D` grow (by `1 + Θ(p)` per
    round), and it comes from the colours removed at the *other* vertices of the edge (the
    "blocking" of the uncoloured, unactivated edges) — so the analysis genuinely needs the
    "coverage" concentration, not just the counting of activated neighbours;
  * expected residual degree: `d(x)(1 - p(1-p/λ)^{rD})`.
* **Do not linearise `(1-p/λ)^{rD}`.**  A round statement whose colour-degree bound uses the
  linearisation `1 - r/(K(1+β))` instead of the exponential `(1-1/(K·λ))^{rD}` can produce a
  *negative* bound (for `r/(K(1+β)) > 1`), which no cardinality satisfies; the exponential form
  (together with the regime hypothesis `λ ≥ (1+β)D` and `r/(K(1+β)) ≤ 1`) is the correct one.
* The concentration of the "coverage" quantities is by a *two-level* argument: condition on the
  activated witnesses (`Ξ`), apply a Chernoff bound to the remaining independent indicators and
  then control the conditional mean, which is itself a weighted sum of independent indicators.
  The exceptional outcomes (`log D` activated edges of one colour at one vertex) are handled by
  excluding them explicitly.
* **The sharp (iterable) colour-degree estimate needs the colour degrees to be *equal* to `D`,
  not merely bounded by it.**  The retention factor of an unactivated edge at a colour `γ` is
  `Π_{g ∩ e ≠ ∅, γ ∈ L(g)}(1-p/|L g|)`, which is *at least* `(1-p/λ)^{rD}` but can be much
  larger when `e` has few `γ`-coloured intersectors (e.g. a star).  Consistency of the
  iteration therefore requires the "embedded"/regularised setting of KKMKO's Proposition
  (`prop:embedding`), which adds vertices/edges so that every colour degree is exactly `D` and
  every vertex lies in exactly `C = r` cliques; equivalently one must carry the whole
  colour-degree *profile* through the iteration.  A round statement with the profile
  (`λ ≤ |L e|`, and the actual degrees as data) is the right interface.

## STATUS and architecture (update)

* `kahnRound_of_core : KahnCoreStatement → KahnRoundStatement` is **proved** (below).  Hence the
  deliverable `kahnRoundStatement` is exactly Kahn's theorem for linear hypergraphs of edges of
  size at least two (`KahnCoreStatement`, paper Theorem 4.6).
* `KahnCoreStatement` is obtained from the **colour-degree nibble** in
  `Submission/Work/Deep/Kahn/NibbleRoundDefs.lean`, whose `RoundStepStatement` is the one-round
  interface (common list size `Λ`, colour-degree bound `D`, retention factors
  `retention = (1 - p/Λ)^(CD)` and `retentionU = (1 - p/Λ)^(D(C-1))`, `p = 1/K`).
* The interface is proved as the composition of four separately delegated lemmas:
  * `Work.Deep.Kahn.nibbleRegularised` (`RegularisedNibbleStatement`) — the probabilistic core,
    for the *regularised* instance (edges of size exactly `C`, lists of size exactly `Λ`,
    occurring colour degrees exactly `D`);
  * `Work.Deep.Kahn.kahnEmbedding` (`EmbeddingStatement`) — the regularisation/embedding
    (`prop:embedding` of arXiv:2109.11438) and its pull-back properties;
  * `Work.Deep.Kahn.nibbleRoundGlue` — the restriction of the embedded outcome to the original
    instance, giving `RoundStepStatement` from the previous two;
  * `Work.Deep.Kahn.kahnCore_of_roundStep` — the iteration of the round (the ratio `Λ/D`
    improves by `1 + Θ(p)` per round until `Λ ≥ 8 C D`) plus the finishing step
    `Work.Deep.Kahn.finishing_step` (Reed's list-colouring-constants lemma) and the gluing of
    the per-round partial colourings.
* A warning recorded in `NibbleRoundDefs.lean`: the colour-degree retention factor has exponent
  `D (C-1)` and **not** `C D`; and the residual lists must be allowed to *contain* colours that
  were removed by unkept activated edges (the interface only requires soundness, i.e. that the
  colours *used* by kept edges are removed).  Both points are needed for the estimate to be true
  and for the ratio to improve.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

/-- The degree of every vertex of the empty hypergraph is zero. -/
lemma hypergraphDegree_of_eq_empty {n : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (h : 𝓖 = ∅) (v : Fin n) : hypergraphDegree 𝓖 v = 0 := by
  rw [h, hypergraphDegree]
  exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => Set.notMem_empty x.1 x.1.2⟩)

/-- The colouring of the empty hypergraph. -/
noncomputable def emptyColoring {n c : ℕ} :
    (∅ : ErdosFaberLovaszConjecture.Hypergraph (Fin n)).Coloring (Fin c) where
  labels := fun e => (e.2 : False).elim
  isColoring := fun e₁ _ _ _ => (e₁.2 : False).elim

/-- Kahn's theorem for edges of size at least two implies the one-round statement: the round
that colours *everything* satisfies both conclusions (`𝓗₀ := 𝓗`).

The proof is bookkeeping: with `𝓗₀ := 𝓗` the progress clause reads
`d_{𝓗∖𝓗}(v) = 0 ≤ (1-θ)·Δ(𝓗)` and the loss clause is vacuous, so it remains to produce a
proper colouring of `𝓗` itself from the lists.  When `(1+β)D ≤ c` this is exactly
`KahnCoreStatement`; when it fails, every edge of `𝓗` has list at most `c < (1+β)D`, hence
`𝓗` is empty and the colouring is trivial. -/
lemma hypergraphMaxDegree_of_eq_empty {n : ℕ}
    {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} (h : 𝓖 = ∅) :
    hypergraphMaxDegree 𝓖 = 0 := by
  rw [h, hypergraphMaxDegree]
  simp [hypergraphDegree]

lemma hypergraphDegree_empty {n : ℕ} (v : Fin n) :
    hypergraphDegree (∅ : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) v = 0 :=
  hypergraphDegree_of_eq_empty rfl v

theorem kahnRound_of_core (h : KahnCoreStatement) : KahnRoundStatement := by
  intro β hβ r hr
  obtain ⟨D₀, hD₀, hcore⟩ := h β hβ r hr
  refine ⟨1 / 2, 1 / 4, by norm_num, by norm_num, by norm_num, D₀, hD₀, ?_⟩
  intro D hD n 𝓗 hlin hmax hsize2 hsize c L hlist
  by_cases hempty : (𝓗 : Set (Set (Fin n))) = ∅
  · -- no edge at all: colour nothing
    refine ⟨∅, (fun _ he => absurd he (by simp)), emptyColoring, ?_, ?_, ?_⟩
    · intro e
      exact (e.2 : False).elim
    · intro v
      rw [hypergraphDegree_of_eq_empty (by rw [hempty]; simp), hypergraphMaxDegree_of_eq_empty hempty]
      norm_num
    · intro e he
      exact absurd (hempty ▸ e.2) he
  · -- at least one edge: the list inequality forces `(1+β) D ≤ c`, and Kahn's theorem
    -- (restricted to edges of size at least two) colours everything
    obtain ⟨e₀, he₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hc : (1 + β) * D ≤ (c : ℝ) := by
      have h1 : (1 + β) * D ≤ ((L ⟨e₀, he₀⟩).card : ℝ) := hlist ⟨e₀, he₀⟩
      have h2 : ((L ⟨e₀, he₀⟩).card : ℝ) ≤ (c : ℝ) := by
        have := Finset.card_le_univ (L ⟨e₀, he₀⟩)
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      linarith
    obtain ⟨φ, hφ⟩ := hcore D hD n 𝓗 hlin hmax hsize2 hsize c hc L hlist
    refine ⟨𝓗, ?_, φ, ?_, ?_, ?_⟩
    · intro e he
      exact he
    · intro e
      simpa using hφ e
    · intro v
      rw [Set.diff_self, hypergraphDegree_empty]
      have : (0 : ℝ) ≤ (1 - 1 / 2) * ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) := by positivity
      simpa using this
    · intro e he
      exact absurd e.2 he

/-- **Kahn's theorem for hypergraphs with edges of size at least two** (paper Theorem 4.6):
the deep input of this subproject.  Its proof is the semi-random (nibble) argument sketched in
the module docstring: the one-round step of `Submission/Work/Deep/Kahn/RoundDefs.lean`,
iterated, followed by the greedy finishing bound
`Work.Deep.Kahn.listColorable_of_card_gt_sum_degree`. -/
theorem kahnCoreStatement : KahnCoreStatement :=
  kahnCore_of_roundStepB (nibbleRoundGlue nibbleRegularised kahnEmbedding)

/-- The requested one-round statement.  It is *equivalent* to `KahnCoreStatement`: the round
that colours every edge satisfies it (`kahnRound_of_core`), and conversely `KahnCoreStatement`
is obtained from it by iteration (`Work.Deep.Kahn.kahnCore_of_round`). -/
theorem kahnRoundStatement : ErdosFaberLovaszConjecture.KahnRoundStatement :=
  kahnRound_of_core kahnCoreStatement

/-- **Kahn's theorem** (paper Theorem 4.6, the deep input of the EFL proof), assembled from
`KahnCoreStatement` through the two proved reductions `kahnList_of_kahnCore` and
`kahnStatement_of_kahnList`. -/
theorem kahnStatement : ErdosFaberLovaszConjecture.KahnStatement :=
  kahnStatement_of_kahnList (kahnList_of_kahnCore kahnCoreStatement)

end Work.Deep.Kahn
