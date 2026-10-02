import Submission.EFL.Nibble
import Submission.EFL.EGJ
import Submission.EFL.Embed

/-!
# The Rödl-nibble chapter: vocabulary

This module is the base of the `Work.Deep.Nibble` chapter, whose target is a
proof of `ErdosFaberLovaszConjecture.NibbleStatement` (Lemma `lem:nibble2` of
Kang–Kelly–Kühn–Methuku–Osthus).

The chapter is organised in three layers.

* **The pseudorandom-matching layer** (`PseudorandomMatchingStatement`,
  Lemma `lem:pseudorandom_matching` of §8): matchings covering prescribed
  fractions of a family of vertex sets, extending prescribed matchings.
* **The EGJ layer**: the matching theorem of Ehard–Glock–Joos
  (`EGJStatement`, `SparseEGJStatement`) from which the pseudorandom-matching
  lemma is derived.
* **The Rödl-nibble layer**: the semi-random engine proving the matching
  theorems.

Here we set up the vocabulary: the vertex support of a multi-hypergraph, the
family of edges through a vertex, the two "pseudorandomness" conclusions of
`lem:pseudorandom_matching`, and the statement itself together with its
asymptotic margin bundle.
-/

set_option autoImplicit false

open scoped BigOperators

/-!
## Status of the chapter (what is proved, and where)

* `Work.Deep.Nibble.Defs` (this module): the vocabulary (`PseudorandomMatchingAt`,
  `AssemblyParams`, `NibbleMarginsStrong`, `NibbleStatementStrong`,
  `NibbleStatementFixed`, `SparseMatchingStatement`, `EdgePartition`,
  `PseudoRandomFam`, `LeftoverFam`) and the note recording the defects of the
  seeded cone statements.
* `Work.Deep.Nibble.Glue`: the API of that vocabulary, including the bridges to
  the cone's `matchVert`/`Covers`/`PseudoRandom`/`PerfectCoverage`/
  `NearlyPerfectCoverage` (`pseudoRandom_famOf_iff` and friends).
* `Work.Deep.Nibble.exists_edgePartition` (PROVED): the random-partition step of
  `lem:nibble2` — a `K`-fold partition of a multi-hypergraph into parts of
  degree-accuracy `δ`, by the probabilistic method with the workspace's
  Chernoff bound.
* `Work.Deep.Nibble.not_nibbleStatement` (PROVED): `¬ NibbleStatement` — the
  seeded target is **false** (its C4 omits the paper's pairwise
  edge-disjointness of the `M i`); see the note below for the counterexample.
* `Work.Deep.Nibble.sparseMatchingStatement_of_EGJStatement` (PROVED):
  `cor:sparse_egj` from `thm:egj`, in the paper's (corrected) quantifier order.
* `Work.Deep.Nibble.pseudorandomMatchingStatement_of_embed_sparseMatching`:
  `lem:pseudorandom_matching` from `lem:embed` + `cor:sparse_egj` (the
  deterministic step of §8).
* `Work.Deep.Nibble.nibbleConclusion_of_assembly`: the §7 assembly — the Nibble
  Lemma's conclusion from the corrected margins, a partition of `𝓗'` and an
  instance of `lem:pseudorandom_matching`, following efl.tex:1737–1836.

The remaining gap to the deliverable `theorem nibbleStatement : NibbleStatement`
is **not** a proof obligation: that statement is false as seeded (defect (5)
below).  The corrected target `NibbleStatementFixed` needs (i) the two cone
statements `EmbedStatement` and `EGJStatement` (the deep inputs of §8), (ii) the
explicit threshold certificate relating `n` to the `n₀` of
`lem:pseudorandom_matching` (the margins `NibbleMarginsStrong` record the
`γρε`-relative hierarchy that makes such an `n₀` reachable), and (iii) the
assembly above.
-/

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

namespace MultiHypergraph

/-- The vertex support `V(𝓜) = {v | 0 < d_𝓜(v)}` of a multi-hypergraph. -/
def verts (𝓜 : MultiHypergraph n) : Set (Fin n) := {v | 0 < 𝓜.deg v}

theorem mem_verts {𝓜 : MultiHypergraph n} {v : Fin n} :
    v ∈ 𝓜.verts ↔ 0 < 𝓜.deg v := Iff.rfl

/-- The family `E_𝓜(w)` of edges of `𝓜` (including the singleton copies)
through the vertex `w`. -/
def edgesThrough (𝓜 : MultiHypergraph n) (w : Fin n) : Set (Set (Fin n)) :=
  {e ∈ 𝓜.edgeSet | w ∈ e}

theorem mem_edgesThrough {𝓜 : MultiHypergraph n} {w : Fin n} {e : Set (Fin n)} :
    e ∈ 𝓜.edgesThrough w ↔ e ∈ 𝓜.edgeSet ∧ w ∈ e := Iff.rfl

/-- The proper edges of `𝓜` through `w`. -/
theorem edgesThrough_subset_edgeSet (𝓜 : MultiHypergraph n) (w : Fin n) :
    𝓜.edgesThrough w ⊆ 𝓜.edgeSet := fun _ h => h.1

end MultiHypergraph

/-! ## The two conclusions of the pseudorandom-matching lemma -/

/-- **Condition NB2** of Lemma `lem:pseudorandom_matching`: the matching `N` is
`(γ,κ)`-pseudorandom with respect to the family `𝓕V` of vertex sets — every
`A ∈ 𝓕V` loses `γ|A| ± κn` vertices to `V(N)`. -/
def PseudoRandomFam (N : Set (Set (Fin n))) (𝓕V : Set (Set (Fin n))) (γ κ : ℝ) : Prop :=
  ∀ A ∈ 𝓕V, |(((A \ famVert N).ncard : ℝ)) - γ * (A.ncard : ℝ)| ≤ κ * (n : ℝ)

/-- **Condition NB3** of Lemma `lem:pseudorandom_matching`: the union of the
matchings `N i` covers all but a `γ`-fraction of every `F ∈ 𝓕E`, up to an
additive error `κ max(|F|,D)`. -/
def LeftoverFam {D : ℕ} (N : Fin D → Set (Set (Fin n))) (𝓕E : Set (Set (Set (Fin n))))
    (γ κ : ℝ) : Prop :=
  ∀ F ∈ 𝓕E, ((F \ ⋃ i : Fin D, N i).ncard : ℝ) ≤
    γ * (F.ncard : ℝ) + κ * max (F.ncard : ℝ) (D : ℝ)

/-! **(4) The `≤ βD` interaction hypothesis of the seeded `NibbleStatement` covers
only `𝓗'.edges`, not `𝓗'.edgeSet`.**  `MultiHypergraph.edges` holds only the
edges of size at least two; the paper's C4 says "for every edge `e ∈ 𝓗'`" of
the multi-hypergraph, i.e. also every singleton copy.  The proof of
`lem:pseudorandom_matching` needs the singleton case: its
`eqn:unif_intersect` (hence the `(1±2β)D` degrees of the auxiliary hypergraph
`𝓗_aux` at the vertices coming from `𝓗'`-edges) is derived through
`ψ(e*) ∈ 𝓗'`, and for a singleton copy `ψ(e*) = {v}`.  The statement below
therefore uses `𝓗'.edgeSet`; the seeded `NibbleStatement` should be corrected
the same way.
-/

/-- **Lemma `lem:pseudorandom_matching`** (the pseudorandom-matching lemma of
§8), as an internal statement of the chapter — in the paper's own asymptotic
form, with the threshold `n₀` existential.

The paper's hypotheses `0 < 1/n₀ ≪ 1/r, β ≪ κ, γ ≪ 1`, `n ≥ n₀`,
`D ∈ [n^{1/2}, n]` are recorded as: for `r ≥ 2` and constants `β κ γ > 0` with
`10β ≤ κ ≤ γ/4 ≤ 1/4`, there is `n₀` such that for all `n ≥ n₀` (and
`n^{1/2} ≤ D ≤ n`) every linear multi-hypergraph `𝓗' ⊆ 𝓗` whose degrees are
`(1±β)D` and whose edges have size at most `r`, every pair of families `𝓕V`,
`𝓕E` of at most `n^{log n}` vertex sets resp. sets of edges, and every family of
`D` edge-disjoint matchings `M i ⊆ 𝓗 ∖ 𝓗'` of at most `βD` vertices each with
each edge of `𝓗'` meeting at most `βD` of the `M i`, there are edge-disjoint
matchings `N i` with `M i ⊆ N i`, `N i ∖ M i ⊆ 𝓗'`, that are
`(γ,κ)`-pseudorandom with respect to `𝓕V` and whose union covers all but a
`γ`-fraction of every member of `𝓕E` (up to `κ max(|F|,D)`). -/
def PseudorandomMatchingStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ β κ γ : ℝ, 0 < β → 0 < κ → 0 < γ →
    10 * β ≤ κ → 4 * κ ≤ γ → γ ≤ 1 →
    ∃ n₀ : ℝ, 0 < n₀ ∧
    ∀ n : ℕ, n₀ ≤ (n : ℝ) → ∀ (𝓗 𝓗' : MultiHypergraph n)
      (𝓕V : Set (Set (Fin n))) (𝓕E : Set (Set (Set (Fin n))))
      {D : ℕ} (M : Fin D → Set (Set (Fin n))),
      (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) → (D : ℝ) ≤ (n : ℝ) →
      𝓗.IsLinear → 𝓗'.IsLinear → 𝓗' ≤ 𝓗 →
      (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
      (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
      (𝓕V.ncard : ℝ) ≤ (n : ℝ) ^ Real.log n →
      (𝓕E.ncard : ℝ) ≤ (n : ℝ) ^ Real.log n →
      (∀ F ∈ 𝓕E, F ⊆ 𝓗'.edges) →
      (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
      (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
      (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
      (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
      (∀ e ∈ 𝓗'.edgeSet,
        (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
      ∃ N : Fin D → Set (Set (Fin n)),
        (∀ i, M i ⊆ N i) ∧
        (∀ i, MultiHypergraph.IsMatching 𝓗 (N i)) ∧
        (∀ i, ∀ e ∈ N i, e ∉ M i → e ∈ 𝓗'.edgeSet) ∧
        (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
        (∀ i, PseudoRandomFam (N i) 𝓕V γ κ) ∧
        LeftoverFam N 𝓕E γ κ ∧
        -- the singleton bookkeeping of the paper's multi-hypergraph reading of
        -- edge-disjointness (needed by the §7 assembly; not implied by `EdgeDisjointFam`)
        (∀ w : Fin n, (({i : Fin D | ({w} : Set (Fin n)) ∈ N i ∧
            ({w} : Set (Fin n)) ∉ M i} : Set (Fin D)).ncard) ≤ 𝓗'.singles w)

/-! ## Two defects in the seeded deep inputs, found while building this chapter

Recorded here because they are load-bearing for any proof of
`NibbleStatement`, and because they are *statements of the cone*
(`Submission/EFL/`), not of this chapter.

**(1) `SparseEGJStatement` (`Submission/EFL/EGJ.lean:60`) is false.**  Its
quantifier order is `∀ r, ∃ n₀, ∀ n ≥ n₀, ∀ κ γ, ...`: the threshold `n₀`
depends only on `r`, so `κ, γ` may be chosen *after* `n`.  The paper's
Corollary `cor:sparse_egj` requires `0 < 1/n₀ ≪ 1/r, κ, γ < 1`, i.e.
`n₀ = n₀(r, κ, γ)`.  With the seeded order the statement is refutable: for
`r = 2`, any `n₀`, take `D` large with `D ≡ 1 (mod 4)`, put
`𝓗 := K_{D+1} ⊔ K_{D+1}` on `n := 2(D+1)` vertices (2-uniform, linear, every
degree exactly `D`), `𝓕 := {V(K_{D+1}^{(1)}), V(K_{D+1}^{(2)})}`,
`γ := 1/2`, `κ := 1/(16(D+1))`.  Every matching covers an *even* number of
vertices of each clique, whereas `γ·(D+1) = (D+1)/2` is odd, so
`|S ∖ V(M)| ≥ 1` while the conclusion demands
`| |S ∖ V(M)| - γ|S| | ≤ 4κ|S| = 1/4`.  (This is the corrected statement
`SparseMatchingStatement` below, which puts `∀ κ γ` before `∃ n₀` and is the
form the paper proves and the form this chapter consumes.)

**(2) `NibbleMargins` (`Submission/EFL/Nibble.lean:265`) is far too weak for
the paper's proof of `lem:nibble2`.**  The bundle records `β ≪ γ` as
`16 * β ≤ γ ^ 2` (i.e. `β^{1/2} ≤ γ/4`), but the paper's route needs a
*constant* `κ` with `β^{1/2} ≪ κ ≪ γ` that simultaneously
(i) dominates the error of `lem:pseudorandom_matching`, whose boundary term is
`γ · |V(M_c)| / n ≥ γ · β · D / n` (the `M_c` are only known to satisfy
`|V(M_c)| ≤ βD`), and
(ii) satisfies `1500 * κ ≤ γ/4` — the §7.2 absorption
(`Submission/EFL/InternalAbsorption.lean`, `InternalMargins.hκγ`) is applied
with pseudorandomness parameter `γ/4`.
Since `β ≤ γ²/16 ≤ 1/256` and `D ≤ n`, (i) and (ii) force
`β D / n ≤ 1/1500`, while `NibbleMargins` permits `βD/n` up to `γ²/16`.  So
already for `γ = 1/4`, `n = 10^6`, `β = 1/256`, `D = 10^4` the proof does not
go through, and `NibbleMargins` is too weak by roughly eight orders of
magnitude in the constant.  The bundle also lacks an `n ≥ n₀(γ,r,ξ,β)`
condition: with `K` parts the absorption's `k ≤ κn` needs
`K ≳ 6000 D/(γ n)`, and the Chernoff bound for the partition needs
`δ² D/K ≳ K log n`, both of which fail for small `n` (e.g. `D = n^{2/3}` and
`n < 10^{13}`).  Consequently `NibbleStatement` as seeded is *not* provable by
the paper's route; whether it is true is open (the conclusion is an existence
statement and no counterexample is known).  See `NibbleMarginsStrong` below
for the corrected bundle used by this chapter. -/

/-- **Corollary `cor:sparse_egj` with the paper's quantifier order.**  This is
the statement the paper proves from `EGJStatement`; it differs from the seeded
`ErdosFaberLovaszConjecture.SparseEGJStatement` by placing `∀ κ γ` *before*
`∃ n₀` (see the note above: with the seeded order the statement is false). -/
def SparseMatchingStatement : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ κ γ : ℝ, 0 < κ → κ ≤ 1 → 0 < γ → γ ≤ 1 →
    ∃ n₀ : ℝ, 0 < n₀ ∧
    ∀ n : ℕ, n₀ ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
    ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → (∀ e ∈ 𝓗, edgeSize e = r) →
      (∀ v : Fin n, |((hypergraphDegree 𝓗 v : ℝ)) - D| ≤ κ * D) →
      ∀ 𝓕 : Set (Set (Fin n)), (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) →
        ∃ M : Set 𝓗, IsMatching 𝓗 M ∧ ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
          |(((S \ matchVert M).ncard : ℝ) - γ * (S.ncard : ℝ))| ≤ 4 * κ * (S.ncard : ℝ)

/-! ## The corrected margin bundle and the §7 assembly interface

The paper's proof of `lem:nibble2` (efl.tex:1737–1836) selects, from the
margins, (i) a constant `κ` with `1/r, ξ, β^{1/2} ≪ κ ≪ γ`, (ii) a partition of
`𝓗'` into `K = ⌈κ⁻¹⌉` parts of accuracy `δ`, and (iii) applies
`lem:pseudorandom_matching` on each part with pseudorandomness parameter
`γ_p`, then one of the §7 absorption lemmas.  The numeric conditions that this
consumes are recorded in `AssemblyParams`; the corrected asymptotic hypothesis
(from which those parameters can be found) is `NibbleMarginsStrong`.

`PseudorandomMatchingAt n r β κ γ` is the *body* of
`PseudorandomMatchingStatement` at a fixed vertex count `n`, i.e. the instance
of `lem:pseudorandom_matching` that the assembly uses. -/

/-- **The instance of `lem:pseudorandom_matching` used by the §7 assembly**:
the body of `PseudorandomMatchingStatement` at a fixed `n` and for fixed
constants `r, β, κ, γ`. -/
def PseudorandomMatchingAt (n : ℕ) (r : ℕ) (β κ γ : ℝ) : Prop :=
  ∀ (𝓗 𝓗' : MultiHypergraph n) (𝓕V : Set (Set (Fin n))) (𝓕E : Set (Set (Set (Fin n))))
    {D : ℕ} (M : Fin D → Set (Set (Fin n))),
    (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) → (D : ℝ) ≤ (n : ℝ) →
    𝓗.IsLinear → 𝓗'.IsLinear → 𝓗' ≤ 𝓗 →
    (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
    (𝓕V.ncard : ℝ) ≤ (n : ℝ) ^ Real.log n →
    (𝓕E.ncard : ℝ) ≤ (n : ℝ) ^ Real.log n →
    (∀ F ∈ 𝓕E, F ⊆ 𝓗'.edges) →
    (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
    (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
    (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
    (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
    ∃ N : Fin D → Set (Set (Fin n)),
      (∀ i, M i ⊆ N i) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓗 (N i)) ∧
      (∀ i, ∀ e ∈ N i, e ∉ M i → e ∈ 𝓗'.edgeSet) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
      (∀ i, PseudoRandomFam (N i) 𝓕V γ κ) ∧
      LeftoverFam N 𝓕E γ κ ∧
      -- the singleton bookkeeping of the paper's multi-hypergraph reading of
      -- edge-disjointness: at most `𝓗'.singles w` of the matchings may add the
      -- singleton `{w}`.  This is *not* implied by `EdgeDisjointFam` (which
      -- deliberately exempts singletons) and is needed by the §7 assembly.
      (∀ w : Fin n, (({i : Fin D | ({w} : Set (Fin n)) ∈ N i ∧
          ({w} : Set (Fin n)) ∉ M i} : Set (Fin D)).ncard) ≤ 𝓗'.singles w)

/-- A `K`-fold partition of the edges of a multi-hypergraph: the proper edges
are split among the parts, and the `𝓜.singles w` copies of the singleton edge
`{w}` are distributed among the parts.  The parts are sub-multi-hypergraphs of
`𝓜` whose degrees sum, at every vertex, to the degree in `𝓜`. -/
structure EdgePartition {n : ℕ} (𝓜 : MultiHypergraph n) (K : ℕ) where
  /-- The parts of the partition. -/
  part : Fin K → MultiHypergraph n
  /-- Every part is a sub-multi-hypergraph. -/
  le : ∀ i, part i ≤ 𝓜
  /-- Every proper edge of `𝓜` lies in exactly one part. -/
  edges_cover : ∀ e ∈ 𝓜.edges, ∃! i, e ∈ (part i).edges
  /-- The degrees of the parts sum to the degree of `𝓜`. -/
  deg_sum : ∀ w : Fin n, (∑ i : Fin K, (part i).deg w) = 𝓜.deg w

/-- **The numeric conditions the §7 assembly needs** on the parameters it
selects from the margins: the constant `κ` (which `lem:pseudorandom_matching`'s
error must fit), the pseudorandomness parameter `γp` passed to the absorption,
the partition accuracy `δ`, the tolerance `βp` at which
`lem:pseudorandom_matching` is applied to a part, and the number `K` of parts.
The `InternalMargins`/`CrossingMargins` fields of
`Submission/EFL/InternalAbsorption.lean`/`CrossingAbsorption.lean` are imposed
on `κ` at `γ_abs = γp`.

**Provenance.**  Every field below was forced by a prover that attempted the
assembly (`nibbleConclusion_of_assembly`, six attempts); the ones marked
"diagnosed" are the conditions those attempts reported as necessary, so they
should be re-derived (not merely asserted) when the §12 numeric layer is
rewritten:

* `hlinH` — the paper's "`𝓗` linear", missing from the seeded
  `NibbleStatement`;
* `hγpγ`, `hγpγup` — `γ ≤ 4γp` and `γp + 2κ ≤ γ`: the absorption is only
  available at `γ_abs = γp`, so the deleted absorber's typicality
  `γ + γp` must be `≤ 10γp` (lower bound on `γp`), while summing
  `LeftoverFam` over the `K` parts must fit clause (6) (upper bound);
* `hKceil`, `hKfloor`, `hKround` — the rounding slack letting the part sizes
  `n_i ∈ {⌊D/K⌋, ⌈D/K⌉}` serve `D` colour classes with every batch of size
  `≤ κn` (diagnosed);
* `hβD'` — each fed matching contains one of the given `M c`, so
  `β D ≤ βp κ n` (diagnosed);
* and the batch decomposition still needs integrality slack, e.g.
  `β * K ≤ βp` (diagnosed).  The robust design is to *choose* `K, δ, βp, κ, γp`
  explicitly from the margins as the paper does (`K := ⌈κ⁻¹⌉` with
  `1/r, ξ, β ≤ γρε/(10^6 K)`) rather than to assert their existence. -/
structure AssemblyParams (n : ℕ) (D β γ ε ρ ξ : ℝ) (κ γp δ βp : ℝ) (K : ℕ) : Prop where
  hκ0 : 0 < κ
  /-- `lem:pseudorandom_matching`'s error fits `InternalMargins.hκγ` at `γ_abs = γp` -/
  hκγ : 1500 * κ ≤ γp
  hκγρ : 4000 * κ ≤ γp * ρ
  hκγε : 8 * κ ≤ γp * ρ * ε
  hκγ2 : 100 * κ ≤ γp ^ 2
  hγp0 : 0 < γp
  /-- the deleted absorber `R_i` is `(ρ, 2γ, ξ)`-typical and the absorption is
  run at typicality parameter `10 * γp`, and `IsAbsorber` is monotone in that
  parameter, so `γp ≥ γ/4` (the paper's choice `γp = γ/4`) -/
  hγpγ : γ ≤ 4 * γp
  /-- the leftover budget: summing `LeftoverFam` over the `K` parts must fit
  clause (6) of the conclusion, giving `γp + 2κ ≤ γ` -/
  hγpγup : γp + 2 * κ ≤ γ
  hγpρ : 20000 * γp ≤ ρ
  hγpε : 40 * γp ≤ ρ * ε
  hγpξε : 4000 * ξ ≤ γp * ρ
  hγpbig : 2000 ≤ γp * ρ * (n : ℝ)
  hγpn : 4 ≤ γp ^ 2 * (n : ℝ)
  hδ0 : 0 < δ
  hδ1 : δ ≤ 1
  hβp0 : 0 < βp
  hβp1 : βp ≤ 1
  /-- the part degrees `(1±δ)(1±β)D/K` are `(1±βp)·n_i`, the tolerance with
  which `lem:pseudorandom_matching` is applied to a part -/
  hβp : 4 * (δ + β + (K : ℝ) / D) ≤ βp
  /-- `lem:pseudorandom_matching`'s own hierarchy `βp ≪ κ` -/
  hβpκ : 10 * βp ≤ κ
  hK : 2 ≤ K
  /-- `n_i = D/K ≥ n^{1/2}`: `lem:pseudorandom_matching`'s lower bound on `D` -/
  hKlow : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ D / (K : ℝ)
  /-- the rounding slack of the chunking: `⌈D/K⌉ ≤ κ n` and
  `⌊D/K⌋ ≥ n^{1/2}`, so that the part sizes `n_i ∈ {⌊D/K⌋, ⌈D/K⌉}` can serve the
  `D` colour classes subject to each batch's `D' ≤ κ n` -/
  hKceil : (K : ℝ) * κ ≥ 1
  hKfloor : (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ κ * D
  hKround : 1 ≤ κ * ((n : ℝ) - D)
  /-- the seeds' size must fit the tolerance of the part they are served by:
  each fed matching contains one of the given `M c`, whose vertex set is only
  known to satisfy `|V(M c)| ≤ βD`, while the batch has `D' = n_i ≈ D/K`
  colours, so `β D ≤ βp κ n` is needed (the last condition found by the
  assembly children) -/
  hβD' : β * D ≤ βp * κ * (n : ℝ)
  /-- the integrality slack of the batch decomposition: with one part per batch
  the colour count of a batch is `n_i ≈ D/K` and the fed matchings contain the
  given `M c`, whose vertex sets are only known to satisfy `|V(M c)| ≤ βD`, so
  `β K ≤ βp` is needed -/
  hβK : β * (K : ℝ) ≤ βp
  /-- the *floor* form of the seed size: the parts have `⌊D/K⌋` colours, and
  `⌊D/K⌋ ≥ D/K - 1` (seventh diagnosis) -/
  hβpfloor : β * D ≤ βp * (D / (K : ℝ) - 1)
  /-- slack in the absorption's `100κ ≤ γp²`: dropping the loose singleton edges
  of the batch matchings before handing them to the absorption costs an extra
  error `βD/n`, so the field must hold with room (seventh diagnosis) -/
  hκγ2' : 200 * κ ≤ γp ^ 2
  /-- the absorption is applied to `n_i = D/K` matchings and needs `n_i ≤ κ n` -/
  hKup : D ≤ κ * (n : ℝ) * (K : ℝ)
  /-- the Chernoff bound of the partition step -/
  hCher : 2 * ((n : ℝ) * (K : ℝ)) *
      Real.exp (-(3 * δ ^ 2 * (1 - β) * D) / (8 * (K : ℝ))) < 1
  /-- the families `𝓕V, 𝓕E` of `lem:pseudorandom_matching` have at most `n^{log n}`
  members -/
  hfam : 2 * (n : ℝ) + 4 ≤ (n : ℝ) ^ Real.log n

/-- **The conclusion of the Nibble Lemma** (clauses N1–N3 and the singleton
bookkeeping of `lem:nibble2`), shared by the cone's `NibbleStatement` and by
`SeededNibbleStatement`. -/
def NibbleConclusion {n : ℕ} (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n))
    {U S : Set (Fin n)} {γ β ε : ℝ} {D : ℕ} (M : Fin D → Set (Set (Fin n))) : Prop :=
  ∃ N : Fin D → Set (Set (Fin n)),
    (∀ i, M i ⊆ N i) ∧
    (∀ i, MultiHypergraph.IsMatching 𝓗 (N i)) ∧
    (∀ i, ∀ e ∈ N i, e ∉ M i → e ∈ 𝓗'.edgeSet ∪ R) ∧
    (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
    (∀ w : Fin n, ((({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin D, N i)).ncard : ℝ) ≤
      γ * (D : ℝ)) ∧
    (∀ w : Fin n, ((({e ∈ 𝓗'.edgeSet | w ∈ e} : Set (Set (Fin n))) \ (⋃ i : Fin D, N i)).ncard : ℝ) ≤
      γ * (D : ℝ)) ∧
    (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N i) U) ∧
    (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N U S) ∧
    (∀ w : Fin n, (({i : Fin D | ({w} : Set (Fin n)) ∈ N i ∧
        ({w} : Set (Fin n)) ∉ M i} : Set (Fin D)).ncard) ≤ 𝓗'.singles w)

/-- **The *seeded* form of `lem:nibble2`** — the statement that was in
`Submission/EFL/Nibble.lean` before 2026-09-22.  It is **false**: its C4 omits
the paper's pairwise edge-disjointness of the `M i` (and it omits `𝓗.IsLinear`,
takes the `≤ βD` interaction bound over `𝓗'.edges` only, and carries the too
weak `NibbleMargins`).  See `Work.Deep.Nibble.not_nibbleStatement` for the
machine-checked refutation.  The cone's current `NibbleStatement` is the
corrected statement. -/
def SeededNibbleStatement : Prop :=
  ∀ {n : ℕ} (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n))
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ γ β ξ ε : ℝ} {D r : ℕ}
    (M : Fin D → Set (Set (Fin n))),
    NibbleMargins n (D : ℝ) r β γ ε ρ ξ →
    U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) →
    S ⊆ U →
    ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ)) →
    U ∈ 𝓥 → (Set.univ : Set (Fin n)) ∈ 𝓥 →
    IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ →
    𝓗' ≤ 𝓗 →
    (∀ e ∈ 𝓗'.edges, e ∉ R) →
    𝓗'.IsLinear →
    (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
    (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
    (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
    (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
    (∀ i, ∀ e ∈ M i, e ∉ R) →
    (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edges, (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
    NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M

end

end ErdosFaberLovaszConjecture
