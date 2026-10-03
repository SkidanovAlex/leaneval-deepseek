import Mathlib
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.coset_lev
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetter_F2_generation
import Submission.Work.OROneRel.gateBookkeeping
import Submission.Work.OROneRel.presentedGroup_union_amalgam
import Submission.Work.OROneRel.unionAmalgam_normalForm
import Submission.Work.OROneRel.bandLineGraphDefs
import Submission.Work.OROneRel.cosetGraph_lineGraph_iso
import Submission.Work.OROneRel.isTree_lineGraph_iff
import Submission.Work.OROneRel.isTree_coset_of_hnnConjMap_injective
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.bandUpBlock

-- NOTE on imports: this file must be importable *together with* `bandUpBlock.lean` (which carries
-- the completed short-deck proof of the crux, `Work.OROneRel.tlH_hnnConjMap_injective`).  The
-- duplicate declaration `Work.OROneRel.mk_lpow` lives in both `tlHalves_inter.lean` and
-- `bandLoopsDefs.lean`, so `tlHalves_inter` (and hence `bandCarrierDefs`, `tlBand_mul_inv_mem_tlH`,
-- `tlTranslate_eq_iff`) may NOT be imported here; the only content that needed it
-- (`tlHk_zero`, `tlH_inf_tlPle`) now lives in `Submission/Work/OROneRel/bandHalvesInter.lean`.

/-!
# The band coset graph is a tree: state of the art (session notes)

Target: `Work.OROneRel.band_cosetGraph_isTree`, i.e. `IsTree (GradedHNN.Coset H₀ τ)` for the band
data (`H₀ = (winRho Wt (tlW p q) 0 (p*q)).range`, `τ = tlLowTau p q hp hq hcop`).

## 1. What the target is, algebraically

With `N := ker (cohom (tlW p q))`, `H_m := τ^m H₀ τ^{-m} ≤ N` and `A := H₀ ⊓ τ⁻¹H₀τ` the target is
(Serre's criterion) the HNN structure `F₂ = HNN(H₀, A, τAτ⁻¹, conj_τ)`; equivalently the
injectivity of `hnnConjMap H₀ τ`.  The generation `⟨H₀, τ⟩ = F₂` is proved
(`Work.OROneRel.twoLetter_F2_generation`), hence connectivity is available
(`GradedHNN.connected_coset`).

## 2. The reduction proved here (purely algebraic, no covering spaces)

`Work.OROneRel.cosetGraph_lineGraph_iso` (`Submission/Work/OROneRel/cosetGraph_lineGraph_iso.lean`)
identifies the coset graph with the **line graph of the chain** `(H_m)` built in
`Submission/Work/OROneRel/bandLineGraphDefs.lean`: vertices `⨿_{m:ℤ} N ⧸ H_m`, two vertices
adjacent when they lie at consecutive levels and the two cosets meet in `N`.

Geometrically, the vertices of the line graph are the lifts of the band `D = winE c 0 (p*q)` to the
universal cover (the band-lifts `g·D̃₀`) and the edges are the lifts of the gates
`D ∩ τ^{±1}D ⊆ Y`; two consecutive lifts are adjacent exactly when they meet.  So the target is

> **the intersection graph of the line of band-lifts is a tree**,

which is the one-dimensional case of Linton's `splitting` (`One-relator hierarchies`,
arXiv 2202.11324, Proposition `splitting` with `2.2.19`), for the band `ℤ`-domain
`D = winE c 0 (p*q) ⊕ (one 2-cell)`:
* (cdt1) `ℤ·D = Y`: `⋃_k τ^k D = Y`;
* (cdt2) `D ∩ τ^k D = ` the induced subgraph on the levels `[k, p*q]` (so the gates *shrink*);
* (cdt3) `D ∩ τD = ` the subgraph on `[1, p*q]` is connected and non-empty (for `(p,q) ≠ (1,1)`);
* the gate inclusions `π₁(D ∩ τ^{±1}D) ↪ π₁(D)` are injective because they are inclusions of
  connected subgraphs of a graph (`Work.OROneRel.winGateFreiheitssatz` gives the algebraic form).

The reduction is *proved* (session 2026), in three pieces (all sorry-free):

* `Work.OROneRel.cosetGraph_lineGraph_iso` — the bijection
  `gH ↦ (φ g, (g * t ^ (-(φ g).toAdd)) · chainPiece …)`, preserving adjacency both ways;
* `Work.OROneRel.isTree_lineGraph_iff` — hence the target is *equivalent* to
  `Work.ORBassSerre.IsTree (lineVertex H₀ τ (cohom (tlW p q)))` for the band data;
* `Work.OROneRel.lineGraph_connected` — connectivity of the line graph from `⟨H, t⟩ = G`
  (for the band: `Work.OROneRel.twoLetter_F2_generation`).

The file below also contains the weight-zero computation `cohom_eq_one_of_mem_winRho_range'`
(the hypothesis `H ≤ ker φ` of the reduction) and the resulting implication
`band_cosetGraph_isTree_of_lineGraph` (the target from the line-graph statement).

## 3. The remaining obligation (the whole content)

**The line-of-groups normal form**: `L` is a tree.  Two points of caution recorded by earlier
sessions and re-verified here:

* the *abstract* meet conditions `H ⊓ ⨆_{i≥1} t^{±i}Ht^{∓i} = H ⊓ t^{±1}Ht^{∓1}` do **not**
  suffice (`Work.OROneRel.cosetGraphIsTree`, `NOTES_meet_conditions_insufficient.md`): they allow
  an element of `H₀` to commute with an element of `τH₀τ⁻¹` "one step away", producing a
  `K_{2,2}`.
* a tempting numerical guess that the tree property could *fail* for `p = 2, q = 3` was **not**
  confirmed: for `p = 2, q = 3` the Bézout data of `twoLetterLowTauBound` is forced (`s = t = 1`),
  so `tlLowTau 2 3 = FreeGroup.of 0 * FreeGroup.of 1`; the ad-hoc Stallings automaton used for the
  check was not a complete decision procedure for `H₀`, so the "diamond" it reported is an
  artefact.  No counterexample to the target is known.

## 3bis. REFUTATION: the "(INT)-descent" of `NOTES_twoLetter_hnnConjMap_routes.md` §10 is INVALID

The reduction chain of that note (implemented in `band_hnnConjMap_injective.lean` and
`tlBandDescent.lean`) claims
> **(INT) ⟹ the crux**,  where (INT) is `tlPle c ⊓ tlPge (c+1) = tlAk c`  (proved, axiom-clean, in
> `tlHalves_inter.lean`),

via the "descent" of §10.3, whose two block lemmas are still `sorry` in `tlBandDescent.lean`.  **The
implication is false and the descent argument is invalid.**  Explicit counterexample, in the
lamplighter group `G = A ⋊ ℤ`, `A = ⊕_{i∈ℤ} ℤ δ_i`, `H = ⟨δ_0⟩`, `t = (0,1)`,
`φ = ` projection onto `ℤ` (the very group used in `cosetGraphIsTree.lean` to refute the meet
conditions):

* `Hk c = t^c H t^{-c} = ⟨δ_c⟩`, `tlPle c = ⟨δ_k : k ≤ c⟩`, `tlPge c = ⟨δ_k : k ≥ c⟩`,
  `Ak c = ⟨δ_c⟩ ⊓ ⟨δ_{c+1}⟩ = 1`; hence `tlPle c ⊓ tlPge (c+1) = 1 = Ak c`, i.e. **(INT) holds**;
  moreover `A = H ∩ t⁻¹Ht = 1` and `B = H ∩ tHt⁻¹ = 1`, so the HNN chain condition
  `g_i ∈ toSubgroup A B u_i → u_i = u_{i+1}` is exactly "`g_i = 1` forces `u_i = u_{i+1}`".
* take `g₀ = δ_0⁻¹`, and the letters `k₁ = δ_1`, `k₂ = δ_0`, `k₃ = δ_1⁻¹`, `k₄ = 1` at levels
  `S = (0,1,0,1,0)`.  Then `k_i ∈ Hk(S_i)`, `|S_{i+1} − S_i| = 1`, `S_0 = S_4 = 0`,
  `g₀ k₁k₂k₃k₄ = δ_0⁻¹ δ_1 δ_0 δ_1⁻¹ = 1`, and *all* the peak/valley outputs required by the
  descent hold — but only vacuously, since `Ak = 1` and `k_i ≠ 1`.  So the descent conclusion
  ("`n = 0`") fails.
* the flaw in §10.3 is the step "`Y = k₁⋯k_j ∈ Ple 0`", where `k_i ∈ Hk(S_i) ⊆ Ple 0` is used for
  `i > j` on the grounds that `S_i ≤ 0` after the end `j` of the *first* excursion above level `1`;
  the level walk may return to positive levels later (here `S_3 = 1`), and then the letters are not
  in `Ple 0`.  (The same defect makes the single-letter base case inapplicable.)
* **consequence**: the band satisfies (INT) *and* every subgroup inclusion used by the descent
  (`Hk c ⊆ Ple c'` for `c ≤ c'`, `Ak c ⊆ Ple c`, `Ak c ⊆ Pge (c+1)`) — so any proof of the crux
  that uses only those data is wrong.  In particular `band_britton` (with the hypotheses it carries
  in `band_hnnConjMap_injective.lean`) is **not** provable from (INT); a correct descent needs
  strictly more input from the band.  Do not re-run the §10.3 plan.

## 4. The surviving route: the geometry of the band carrier

The genuinely band-specific input is the **slice structure of the band carrier in the Cayley tree
`𝒯` of `F₂`** (vertex set `F₂`; level of `v` is `cohom (tlW p q) v`):

* `Work.OROneRel.tlBand p q`, `Submission/Work/OROneRel/bandCarrierDefs.lean`: the elements of `F₂`
  whose reduced spelling walks inside the band `[0, p*q]` — the vertex set of the band's lift;
* **(K)** [`Work.OROneRel.tlBand_mul_inv_mem_tlH`, delegated]: if `v, w ∈ tlBand` have
  `cohom v = cohom w` then `v * w⁻¹ ∈ tlH`.  Equivalently: the level-`m` slices of the carrier are
  single right cosets of `tlH`, so **the translates of the carrier at the same level are either
  equal or disjoint**.  (This is *not* a consequence of (INT): the lamplighter satisfies (INT) and
  fails (K) — its translates at level `0` are `n + ⟨δ_0⟩`-cosets, which are disjoint, but nothing
  at level 1 `⊆` ... ; more to the point, (INT) alone was refuted above.)
* the coset graph `L = Coset H₀ τ` is the graph on the translates `g • tlBand` (i.e. `F₂ ⧸ H₀`)
  with an edge for each consecutive-level meeting, equivalently `{gH₀, gτH₀}` — that is
  `cosetGraph_lineGraph_iso` read in the carrier picture;
* with (K), `L` becomes the intersection graph of a family of **subtrees of the tree `𝒯`** which
  are (i) pairwise disjoint within a level, (ii) each covering exactly the level interval
  `[φ(g), φ(g)+N]`, (iii) mutually congruent (`g • tlBand`).

**Caution** (found this session): the *naive* tree statement "a cyclic sequence of subtrees of a
tree, consecutive ones meeting, distinct ones disjoint within a level, is impossible" is **FALSE**.
Counterexample: in the path `b—c—d—e—f—g`, take levels `S = (0,1,2,3,2,1)` and
`X₀ = {b,c,d,e,f}`, `X₁ = {b,c}`, `X₂ = {c,d}`, `X₃ = {d,e}`, `X₄ = {e,f}`, `X₅ = {f,g}`: all
hypotheses hold (consecutive intersections non-empty, same-level sets disjoint, no backtracking) but
`X₀–X₁–X₂–X₃–X₄–X₅–X₀` is a genuine 6-cycle.  The sets there are *not* congruent and do not carry
the level-interval structure, so (iii) is essential; a proof must use it.

Partial results towards the geometric argument (all from (K) plus elementary tree facts):

* the `K_{2,2}` with both pairs at *consecutive* levels (level pattern `(0,1,0,1)`) is impossible:
  two same-level translates `X₀, X₂` are disjoint, and any two connected sets meeting both contain
  the (unique) bridge between them, hence meet each other — contradicting same-level disjointness
  for `X₁, X₃`.  This is the *true* version of the refuted `Work.OROneRel.coset_two_common_nbrs`,
  and it shows that "no `K_{2,2}` with equal levels" is available unconditionally for the band.
* the *other* possible level pattern of a `4`-cycle is `(0,1,2,1)`.  Parametrising the edges as
  `{aH, aτH}` and writing `B = hnnEdgeB H₀ τ = H₀ ∩ τH₀τ⁻¹ = τ A τ⁻¹` (`A = hnnEdgeA H₀ τ`), the
  computation gives: such a 4-cycle exists **iff** there are `b ∈ H₀ ∖ B`, `β ∈ B`,
  `γ ∈ τBτ⁻¹` with `bβγ ∈ B`, i.e. **iff** `(B · τBτ⁻¹) ∩ H₀ ⊄ B`.  (Sketch: vertices
  `x₀ = H₀`, `x₁ = τH₀`, `x₂ = τhτH₀`, `x₃ = τhτh'τ⁻¹H₀` with `h, h' ∈ H₀`, the last edge forcing
  `x₃ ∈ H₀τH₀/H₀`, which after substituting `b = τâτ⁻¹`, `h, h'` becomes exactly the displayed
  condition; the cycle is non-degenerate iff `a₄ ∉ B`.)  In subgraph terms
  `B = π₁(Λ([1,N]))`, `τBτ⁻¹ = π₁(Λ([2,N+1]))`, `H₀ = π₁(Λ([0,N]))`, so the condition is the
  question whether the "product" `π₁(Λ([1,N])) · π₁(Λ([2,N+1]))` meets `π₁(Λ([0,N]))` outside
  `π₁(Λ([1,N]))`.  For the band this must **fail** (the target is a true theorem); deciding it is
  the sharpest concrete form of the remaining obligation, and it is a genuine free-group
  computation (the relevant indices have ranks `N-p-q+1`, `N-p-q+1`, `N-p-q` respectively, so
  Howson's formula alone does not decide it).
* **warning**: "no `4`-cycle" is *not* sufficient, since longer cycles are not excluded by the
  level arguments above (see the explicit 6-cycle counterexample to the naive tree statement).

## 5. Status and route (for a later stretch)

**Done this session** (all axiom-clean, no `sorry`), the plumbing around the crux:

1. `Work.OROneRel.tlBand_mul_inv_mem_tlH` (file `Submission/Work/OROneRel/tlBand_mul_inv_mem_tlH.lean`)
   — the key structural lemma **(K)**.
2. `Work.OROneRel.tlTranslate_eq_iff` (file `Submission/Work/OROneRel/tlTranslate_eq_iff.lean`) —
   the vertex dictionary `g • tlBand = g' • tlBand ↔ g⁻¹g' ∈ H₀`, i.e. `Stab(tlBand) = H₀`.
3. `Work.OROneRel.isTree_coset_of_hnnConjMap_injective`
   (file `Submission/Work/OROneRel/isTree_coset_of_hnnConjMap_injective.lean`) — pure Bass--Serre
   bookkeeping: injectivity of `hnnConjMap H t` plus `H ⊔ ⟪t⟫ = ⊤` gives `IsTree (Coset H t)`; the
   child also isolated `Work.OROneRel.britton_of_injective`, the Britton statement for the pair
   `(H, t)` *derived from* injectivity.
4. `Work.OROneRel.band_cosetGraph_isTree_of_hnnConjMap_injective` (this file) — the target now
   reduces in one line to the **injectivity of `hnnConjMap H₀ τ`** for the band.

**Remaining obligation** (the crux, unchanged in content): `Function.Injective (hnnConjMap H₀ τ)`
for `H₀ = winRho.range`, `τ = tlLowTau p q` — equivalently Linton's one-dimensional splitting for
the band ℤ-domain, equivalently the tree property itself.  Two surviving strategies:

* **geometric**: prove the tree statement for the family of subtrees `g • tlBand` of the Cayley tree
  of `F₂` (with (K), the level-interval structure and congruence; see §4 — note the naive version is
  FALSE, and the `(0,1,2,1)` case reduces to the free-group computation
  `(B·τBτ⁻¹) ∩ H₀ ⊄ B`).  The dictionary needed to connect this to `Coset H₀ τ` is items 1--3 above.
* **algebraic**: the free-factor/handle elimination of `NOTES_twoLetter_hnnConjMap_routes.md` §8.2
  (`H₀ = π₁([0, N−1]) ∗ ⟨tlU p q⟩`, `τ`'s walk inside the lower gate, Shenitzer rank bookkeeping),
  i.e. a Tietze computation; or a direct proof of `band_britton`
  (`Submission/Work/OROneRel/band_hnnConjMap_injective.lean`) followed by the standard
  "Britton ⟹ injectivity" step.

**Do not** attempt the (INT)-descent of `NOTES_twoLetter_hnnConjMap_routes.md` §10/§11 (its block
lemmas in `tlBandDescent.lean` are unprovable as stated: see §3bis).

## 5bis. The state after the present session (reduction to a *single*, correctly stated hard step)

The target is now reduced — through proved lemmas only — to **one** statement about the band, namely
the corrected ("two-guard") up-block lemma

> `Work.OROneRel.bandUpBlock` (`Submission/Work/OROneRel/bandUpBlock.lean`, delegated this session):
> for a `±1` level walk `t : Fin n → ℤ` with `t 0 = t (n-1) = b` and `t i ≥ b`, and letters
> `y i ∈ tlHk (t i)`, if `y i ∉ tlAk (t i - 1)` at every **peak** of `t` (prev = next = `t i - 1`)
> and `y i ∉ tlAk (t i)` at every **valley** (prev = next = `t i + 1`), then
> `∏ y ∉ tlPle (b - 1)`.

The chain is

* `Work.OROneRel.isTree_coset_of_britton` (§7, proved here): Britton for the pair `(H₀, τ)` — i.e.
  *no nonempty pinch-free word `h₁τ^{ε₁}⋯hₙτ^{εₙ}` with all `hᵢ ∈ H₀` represents an element of `H₀`*
  — implies `IsTree (Coset H₀ τ)`, because a reduced closed path lifts (`hnnLiftAux`) to such a word.
* the pinch-free word is transported to the **walk form** `k₁⋯kₙ = x ∈ H₀` with
  `kᵢ = τ^{S_{i-1}}hᵢτ^{-(S_{i-1})} ∈ H_{S_{i-1}}`, `Sᵢ = ε₁+⋯+εᵢ`, `Sₙ = 0`; pinch-freeness at a
  turn translates (`tlK_notMem_tlAk_of_peak` / `tlK_notMem_tlAk_of_valley`, proved) into exactly the
  two guards of `bandUpBlock`.
* `bandUpBlock` extracts a contradiction by peeling the walk: let `m = min S` and conjugate by
  `τ^{-m}` (this shifts all levels by `-m`, so the walk becomes `≥ 0` and the target `H₀` becomes
  `H_{-m}`; pinch-freeness is conjugation-invariant); then the first excursion of the walk above
  level `0` (which exists because the walk returns to its base) is a walk as in `bandUpBlock` with
  `b ≥ 1`, whose `y`'s are the letters of the excursion, and whose product is a *block*
  `z ∉ tlPle (b-1)` of the word `x`; iterating this peeling (the workspace's `first_return` /
  `firstExcursion_up` provide the combinatorics) produces a word with no letters at all, whence
  `n = 0`.

Two warnings established this session:

* the conjunction of `(INT)` — proved, `tlHalves_inter`, and the source of the corollary
  `tlH_inf_tlPle` proved in §6 below — with the subgroup inclusions is **not sufficient for
  `bandUpBlock`**: the abelian model `V ⋊ ℤ` with `H_k = ℤδ_k`, `τ = t` satisfies `(INT)` and both
  guards while `∏ y = 1`.  The proof must use the band's specific geometry (e.g. `htree`).
* statements whose gate is the *group-theoretic* `tlAk (c-1) = tlHk (c-1) ⊓ tlHk c` instead of the
  band's *van Kampen* gate are **false**: the reviewer of this session's first delegation found the
  explicit counterexample `y₁ = ab⁻²a⁻²b⁻¹a⁻¹`, `y₂ = abab⁻¹a⁻²`, `y₃ = a²bab²a⁻¹` at `p = 2, q = 3`
  (recorded in `upBlock_not_mem_tlPle.lean`) with `y₁y₂y₃ = 1`, `y₁, y₃ ∈ tlHk 1`, `y₂ ∈ tlHk 0`,
  and `y₂ ∈ tlHk 0 ⊓ tlHk 1`; the two-guard form of `bandUpBlock` excludes exactly this witness
  (its valley guard at `i = 2` demands `y₂ ∉ tlAk 0`, which fails).

## 5quater. Refutations produced *by the fleet* in this session (record before delegating again)

Two attempted reductions were handed out this session and both came back `declare_false` with
concrete witnesses; both are now machine-verifiable in the workspace:

* **`Work.OROneRel.mem_tlPle_of_walkP` is FALSE** (the "lower-half walk dictionary" claimed in
  §14.15 of the notes to have "no restriction on `c`"): at `p = 2`, `q = 3`, `c = -5 = 1 - p*q` the
  word `L = [b, a, b, a⁻¹, b⁻¹, b⁻¹]` (the reduced word of `x = b·a·b·(b²a)⁻¹`) has `lsig = 0`, its
  decorated walk visits `0, -2, 1, -1, -4, -2, 0` (so `walkP (tlW 2 3) 0 (· ≤ c + p*q = 1) L`
  holds), but `x ∉ tlPle (-5)`.  This is the content of the *sorry-free*
  `Submission/Work/OROneRel/halfPlane_loop_not_mem_tlPle.lean`
  (`Work.OROneRel.halfPlane_loop_not_mem_tlPle`, `Work.OROneRel.halfPlaneX_not_mem_tlPle`), modulo
  the single sorried finite computation `Work.OROneRel.halfPlaneW_reduced_peak` (the walk of `τ`
  reaches level `m ≥ 3`).  So the walk bound `c + p*q` does **not** imply membership in `tlPle c`;
  the descent of §14.12 step 3 cannot be driven by that statement.
* **The single-guard block lemma is FALSE** (§14.7/§14.13) with the `p = 2, q = 3` witness recorded
  in `upBlock_not_mem_tlPle.lean`; the *two-guard* form is the delegated `Work.OROneRel.bandUpBlock`
  (`Submission/Work/OROneRel/bandUpBlock.lean`), which is **not** refuted by that witness (its
  valley guard excludes it) but whose truth is not settled.

Consequence for the next session: the two "engines" the notes propose for the level descent have
both collapsed *as stated*, and any further delegation in this area must first reproduce the
counterexample search of `Scratch/refute_walkP.lean` and `halfPlane_loop_not_mem_tlPle.lean` against
the *proposed* statement.  The only inputs of the crux that survive contact with the fleet are
(i) `tlHalves_inter` (`(INT)`, proved) and its corollary `tlH_inf_tlPle` (§6), (ii) the carrier
dictionary `tlTranslate_eq_iff` / `tlBand_mul_inv_mem_tlH`, and (iii) `mem_tlH_walkP` /
`tlH_walkP` (the *two-sided* walk characterisation of `tlH` itself).

## 5ter. Reading `NOTES_twoLetter_hnnConjMap_routes.md` §14 *before* delegating (lesson of this session)

The route through the *single-guard* up-block lemma is **dead**, and this was already recorded in the
notes: §14.7/§14.10/§14.13 report `declare_false` verdicts from the fleet's provers for
`upBlock_not_mem_tlPle` (refuted by the concrete `p = 2, q = 3` witness above) and for the abelian
models.  The *two-guard* form (peak guard `∉ tlAk (t i - 1)`, valley guard `∉ tlAk (t i)`) — which is
what the HNN chain condition actually yields (`tlK_notMem_tlAk_of_peak`,
`tlK_notMem_tlAk_of_valley`) and what `bandUpBlock` states — is *not* refuted by that witness, but
§14.13/§14.15 also warn that the block-lemma *layer* may be unusable, and §14.12/§14.15 prescribe the
alternative engine: run the level descent of §7 above through the **walk dictionary**
(`Work.OROneRel.mem_tlPle_of_walkP`, `Work.OROneRel.mem_tlPge_of_walkP`, the completed
`Work.OROneRel.walkP_of_mem_tlPle_v2`) rather than through a block lemma, using
`walkP_reduce`/`walkP_shift_up`/`walkP_shift_down` for the explicit walk confinement of the letters.
The next session should start by deciding between

* (i) `bandUpBlock` (in flight, `Submission/Work/OROneRel/bandUpBlock.lean`) plus the peeling
  assembly sketched in §5bis, and
* (ii) the walk-confinement descent of §14.12/§14.15, which avoids the block layer entirely,

and should read §14 of the notes in full before committing.
-/

namespace Work.OROneRel

/-! ## §6 The two chains of the descent (this session)

The reduction of the target now goes

`IsTree (Coset H₀ τ)`  ⟸  (Britton for `(H₀, τ)`)  ⟸  (the descent of §7 below),

and the *new* proved input of the descent is the **consequence of the intersection formula (INT)**
recorded as `tlH_inf_tlPle`:

> an element of the band vertex `H₀` that lies in the lower half `tlPle (-1) = ⟨H_k : k ≤ -1⟩`
> automatically lies in the *gate* `H₀ ∩ H_{-1}`:
> `H₀ ⊓ tlPle (-1) = H₀ ⊓ tlHk (-1)`.

Indeed `H₀ = tlHk 0 ⊆ tlPge 0`, so `H₀ ⊓ tlPle (-1) ⊆ tlPge 0 ⊓ tlPle (-1) = tlAk (-1) = H_{-1} ⊓ H₀`
by `tlHalves_inter` at `c = -1`, and conversely `tlAk (-1) ⊆ tlPle (-1) ⊓ tlHk 0`.  This is exactly
the "one step of the descent at a peak" that the *r = 1* case of the alternating-product normal form
needs (see §7). -/

/-! ## §7 The descent, and its one remaining input

**The descent.**  Let `h₁τ^{ε₁}⋯hₙτ^{εₙ} ∈ H₀` be a pinch-free word (`hᵢ ∈ H₀`, `n ≥ 1`); in the
conjugated form `kᵢ = τ^{S_{i-1}}hᵢτ^{-(S_{i-1})} ∈ H_{S_{i-1}}` (with `S_i = ε₁+⋯+ε_i`, `S_n = 0`)
it reads

  `k₁⋯kₙ = x ∈ H₀`,   `kᵢ ∈ H_{S_{i-1}}`,   `|S_i - S_{i-1}| = 1`,   `S_n = 0`,

and pinch-freeness says: at every turn of the level walk `S` (i.e. whenever `S_{i+1} = S_{i-1}`) the
letter after the turn satisfies `k_{i+1} ∉ H_{S_i} ∩ H_{S_{i-1}}` (equivalently, by `tlH_inf_tlPle`
and `tlHalves_inter`, `k_{i+1} ∉ tlPle (S_i - 1)` at a local maximum and `k_{i+1} ∉ tlPge (S_i + 1)`
at a local minimum).

The argument concludes by looking at the maximum level `M` of the walk and at the alternating
decomposition `x = A₀b₁A₁⋯b_rA_r` with `b_s` the letters of level `M` (isolated, since `M` is the
maximum) and `A_s ∈ tlPle (M-1)`.  Two cases:

* `r = 1`: `b₁ = A₀^{-1}xA₁^{-1} ∈ tlPle (M-1)` (all three factors are there) — but the pinch at the
  turn at level `M` says `b₁ ∉ H_M ∩ H_{M-1} = H_M ⊓ tlPle (M-1)`; contradiction.  This case only
  uses `tlH_inf_tlPle` (i.e. `(INT)`) and is the *provable* half.
* `r ≥ 2`: here `(INT)` is **not** enough (the lamplighter satisfies `(INT)` and all the inclusions
  and falsifies the conclusion, see §3bis) — this is the genuinely band-specific input, the
  *normal form of the line of groups* `(H_k)`, equivalently van Kampen on the cover of the level
  graph `Y_ℤ` by the bands `D_k = τ^k·D`, and it is delegated as
  `Work.OROneRel.tlPle_amalgam_normalForm` (see the request accompanying this file).

Given the normal form, the descent is completed as: let `M` be the maximum level, `j` the first index
with `S_{j-1} = M`; then `k₁⋯k_j ∈ tlPle (M-1)` (all levels before `j` are `< M`) and `x ∈ H₀ ⊆
tlPle (M-1)` (as `M ≥ 1` after conjugating by `τ^{-l}`, `l = min S`), so the tail product
`k_{j+1}⋯k_n ∈ tlPle (M-1)`.  Splitting the tail at its own occurrences of level `M` writes it as
`b · A₁ · b₂ ⋯` with `b` the leading block of level-`M` letters and the `b_s ∉ tlPle (M-1)` (by the
pinch at the turns at level `M`); the normal form then forces the tail to have no level-`M` letter at
all, whence `k_{j+1} ∈ tlPle (M-1) ∩ H_M = tlHk (M-1)`, contradicting the pinch at the turn at
`S_j = M`.  Iterating, `n = 0`.
-/

/-- **Britton for an HNN pair implies that the coset graph is a tree.**  A reduced closed path in
`GradedHNN.Coset H t` lifts (`hnnLiftAux`) to a pinch-free word representing an element of `H`
(`noPinch_hnnLiftAux`, `hnnLiftAux_vertex`), so if no nonempty pinch-free word represents an element
of `H`, the graph is acyclic; and it is connected by `GradedHNN.connected_coset`. -/
theorem isTree_coset_of_britton {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (hbritton : ∀ L : List (ℤˣ × ↥H), NoPinch H t L → hnnWord H t L ∈ H → L = []) :
    Work.ORBassSerre.IsTree (GradedHNN.Coset H t) := by
  refine ⟨fun x y => GradedHNN.connected_coset H t hgen x y, ?_⟩
  intro a p hp
  by_contra hne
  have hlen : p.length ≠ 0 := fun h0 => hne (Quiver.Path.eq_nil_of_length_zero p h0)
  obtain ⟨g₀, hg₀⟩ := Quotient.exists_rep a
  have hLlen : (hnnLiftAux H t a g₀ hg₀ a p).1.length = p.length :=
    hnnLiftAux_length H t a g₀ hg₀ a p
  have hneL : (hnnLiftAux H t a g₀ hg₀ a p).1 ≠ [] := by
    intro hnil
    rw [hnil] at hLlen
    exact hlen hLlen.symm
  have hprod : hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1 ∈ H := by
    have hvert := hnnLiftAux_vertex H t a g₀ hg₀ a p
    have h1 : (g₀ * hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1)⁻¹ * g₀ ∈ H :=
      (GradedHNN.cmk_eq_iff H t).mp (by rw [hvert]; exact hg₀.symm)
    have h2 : (g₀ * hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1)⁻¹ * g₀
        = (hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1)⁻¹ := by group
    rw [h2] at h1
    simpa using H.inv_mem h1
  exact hneL (hbritton _ (noPinch_hnnLiftAux H t a g₀ hg₀ a p hp) hprod)

/-! ## The weight of the band subgroup

The loop classes generating `winRho.range` have weight `0`, so the band subgroup lies in the kernel
of the weight `cohom (tlW p q)`; this is the hypothesis `H ≤ ker φ` of the reductions
`Work.OROneRel.cosetGraph_lineGraph_iso` and `Work.OROneRel.isTree_lineGraph_iff`. -/

/-- The loop class of a non-tree edge of the window is killed by the weight. -/
theorem cohom_coverClassAt_winBeta {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : winBeta Wt c lo hi) :
    cohom c (winRho Wt c lo hi (FreeGroup.of e)) = 1 := by
  rw [winRho_of, coverClassAt, gaugeMap_of]
  rw [map_mul, map_mul, map_inv, hcoh, hcoh, cohom_of, ← ofAdd_add, ← ofAdd_neg, ← ofAdd_add,
    add_neg_cancel]
  rfl

/-- **The band subgroup has weight zero.** -/
theorem cohom_eq_one_of_mem_winRho_range' {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    (lo hi : ℤ) (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) {g : FreeGroup α}
    (hg : g ∈ (winRho Wt c lo hi).range) : cohom c g = 1 := by
  obtain ⟨x, rfl⟩ := hg
  induction x using FreeGroup.induction_on with
  | one => simp
  | of e => exact cohom_coverClassAt_winBeta Wt c lo hi hcoh e
  | inv_of e ih =>
      show cohom c (winRho Wt c lo hi (FreeGroup.of e)⁻¹) = 1
      rw [map_inv, map_inv]
      exact inv_eq_one.mpr ih
  | mul x y hx hy =>
      show cohom c (winRho Wt c lo hi (x * y)) = 1
      rw [map_mul, map_mul, hx, hy, one_mul]

/-- **The reduction of the target to the line graph of the band chain.**

If the line graph of the chain `τ ^ m * H₀ * τ ^ (-m) ≤ ker (cohom (tlW p q))` is a tree, then so is
the band coset graph — the statement the target asks for.  Conversely (by
`Work.OROneRel.isTree_lineGraph_iff`) the two statements are equivalent, so this is exactly the
remaining obligation. -/
theorem band_cosetGraph_isTree_of_lineGraph (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    (∀ (hH : (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range ≤
        (Work.OROneRel.cohom (Work.OROneRel.tlW p q)).ker),
        Work.ORBassSerre.IsTree (Work.OROneRel.lineVertex
          (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
          (Work.OROneRel.tlLowTau p q hp hq hcop)
          (Work.OROneRel.cohom (Work.OROneRel.tlW p q)) hH)) →
    Work.ORBassSerre.IsTree (Work.OROneRel.GradedHNN.Coset
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop)) := by
  intro hL
  have hH0 : (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0
      ((p : ℤ) * (q : ℤ))).range ≤ (Work.OROneRel.cohom (Work.OROneRel.tlW p q)).ker :=
    fun x hx => cohom_eq_one_of_mem_winRho_range' Wt (Work.OROneRel.tlW p q) 0
      ((p : ℤ) * (q : ℤ)) hcoh hx
  exact (Work.OROneRel.isTree_lineGraph_iff _ _ (Work.OROneRel.cohom (Work.OROneRel.tlW p q))
    hH0 (Work.OROneRel.tlLowTau_cohom p q hp hq hcop)).mpr (hL hH0)

/-- **The target from the injectivity of the HNN comparison map of the band pair.**

This isolates the *whole* remaining mathematical content of
`Work.OROneRel.band_cosetGraph_isTree` as the injectivity of

`hnnConjMap H₀ τ : HNN(↥H₀, H₀ ⊓ τ⁻¹H₀τ, τ(H₀ ⊓ τ⁻¹H₀τ)τ⁻¹, conj_τ) →* F₂`,

i.e. `F₂ = HNN(H₀, H₀ ⊓ τ⁻¹H₀τ, τ(H₀ ⊓ τ⁻¹H₀τ)τ⁻¹, conj_τ)` (Linton's one-dimensional splitting
for the band).  The proof is bookkeeping: `Work.OROneRel.isTree_coset_of_hnnConjMap_injective`
(Bass--Serre: a coset graph is the tree of the HNN extension as soon as the comparison map is
injective) applied to the generation `H₀ ⊔ ⟪τ⟫ = ⊤` (`Work.OROneRel.twoLetter_F2_generation`). -/
theorem band_cosetGraph_isTree_of_hnnConjMap_injective (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hinj : Function.Injective (Work.OROneRel.hnnConjMap
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop))) :
    Work.ORBassSerre.IsTree (Work.OROneRel.GradedHNN.Coset
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop)) :=
  Work.OROneRel.isTree_coset_of_hnnConjMap_injective _ _
    (Work.OROneRel.twoLetter_F2_generation p q hp hq hcop Wt hW0 hcoh hwin htree) hinj

theorem band_cosetGraph_isTree (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    Work.ORBassSerre.IsTree (Work.OROneRel.GradedHNN.Coset
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop)) :=
  Work.OROneRel.band_cosetGraph_isTree_of_hnnConjMap_injective p q hp hq hcop Wt hW0 hcoh hwin
    htree (Work.OROneRel.tlH_hnnConjMap_injective p q hp hq hcop Wt hW0 hcoh hwin htree)

end Work.OROneRel
