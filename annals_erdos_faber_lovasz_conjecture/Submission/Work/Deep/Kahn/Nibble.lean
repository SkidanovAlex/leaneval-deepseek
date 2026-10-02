import Submission.Work.Deep.Kahn.Defs

/-!
# The Rödl-nibble decomposition of Kahn's theorem

The proof of `KahnCoreStatement` is organised as an iterated semi-random
("nibble") procedure.  This module fixes

* the notion of the **colours lost** by an uncoloured edge in one round of the
  procedure, and of the **residual degree** after a round;
* `KahnRoundStatement` — the **one-round step**: a partial proper colouring that
  removes a constant fraction `θ` of the edges at *every* vertex while eating at
  most a fraction `ψ < θ` of the list of every uncoloured edge;
* `KahnCoreStatement` — Kahn's theorem for edges of size at least two;
* `kahnCore_of_round` — the reduction: iterating the one-round step while the
  slack `(list size)/(degree)` grows by the factor `(1-ψ)/(1-θ) > 1` at every
  round, a bounded number of rounds brings the hypergraph into the range of the
  greedy list-colouring bound (`listColorable_of_card_gt_sum_degree`).

The one-round step `KahnRoundStatement` is the deep input of this subproject
(its proof is the semi-random method, i.e. Kahn's 1996 argument).

## Does the one-round step have the same strength as the theorem?

Yes, essentially.  The point of the one-round statement is that its hypotheses
are *the same shape* as the theorem's hypotheses (`Δ ≤ D` and lists of size
`(1+β)D`) at every intermediate stage of the iteration, so the round can colour
*everything* and be trivially applicable; conversely the iteration of the round
proves the theorem.  Kahn's theorem is therefore not reduced here to "easier"
mathematics --- it is reduced to the semi-random **analysis** of one round,
which is where all the difficulty of Kahn's paper sits.  The iteration
(`kahnCore_of_round`) and the finishing arguments are bookkeeping.

## What is proved about the round, and what is missing

Proved and available to a prover of `KahnRoundStatement`:

* `kahnCore_of_round` (file `kahnCore_of_round.lean`): the iteration of the
  round and the greedy finish, i.e. `KahnRoundStatement → KahnCoreStatement`;
* `lostColours_subset_of_palette`: a round drawn from a fixed palette only ever
  loses palette colours;
* `lostColours_card_le_sum_degree` (file `lostColours_card_le_sum_degree.lean`):
  the *naive* (alignment-free) loss bound
  `|lostColours| ≤ ∑_{v ∈ e} d_{𝓗₀}(v)`.  The whole difficulty of the round is
  to improve this by a factor `r` (the number of vertices of `e`) — see the
  warnings below;
* `exists_partialColoring_of_matchings` (file
  `exists_partialColoring_of_matchings.lean`): given edge-disjoint matchings
  `m i` with `γ i ∈ L e` for `e ∈ m i`, the assignment `e ↦ γ i` is a proper
  partial colouring respecting the lists on `⋃ i, m i`.  This is the "last
  step" of any construction of the round: the round is built by finding, for
  each colour of a set of `θΔ` colours, a near-perfect matching, and this lemma
  turns the family of matchings into the partial colouring that the round
  statement asks for.

Missing: the construction of the matchings (the semi-random step itself).

## Warnings for anyone proving `KahnRoundStatement`

* The progress must be measured against `Δ(𝓗)` and not against `d_𝓗(v)`
  vertex by vertex: for the "star" hypergraph with edges `{v, w_i}`
  (`i = 1, …, D`), no round with `θ < 1` colours all of `{v, w_1}, …, {v, w_D}`
  at once (matchings through `v` have one edge), so a per-vertex proportional
  progress `d'(v) ≤ (1-θ) d(v)` is not achievable for the degree-one vertices
  `w_i`.  The `Δ(𝓗)`-form used here is satisfied by the round that colours
  everything.
* A strengthening in which the round is required to draw *all* of its colours
  from one fixed global palette `P` with `|P| ≤ θD` is **false**: take two
  non-adjacent vertices `v, v'` of a graph, each of degree `Δ`, whose incident
  edges have pairwise disjoint lists; the `≥ θD` edges of `v` that must be
  coloured need `θD` distinct colours from their own lists, and likewise at
  `v'`, but the `v`-lists and `v`-lists are disjoint, so `|P| ≥ 2θD`.
  A palette must therefore be handled per-vertex (or per "colour-class"), which
  is why the round statement does not mention a palette.
* The mechanism that makes the loss bound possible is the *alignment* of the
  colours used at the vertices of an edge: at a vertex whose degree is close to
  `Δ`, about `θΔ` colours are used, and an uncoloured edge must lose only a
  `ψ < θ` fraction of its list, which fails for a naive random per-edge colour
  choice (each of the `r` vertices can contribute disjoint lost sets).  Kahn's
  proof achieves the alignment by building colour classes in parallel as
  near-perfect matchings, one per colour, over a set of colours of size `θΔ`
  (the semi-random "nibble"), and controlling the losses by concentration.
* The "large palette" regime `c ≫ ℓ` needs a different estimate from the
  "small palette" regime `c ≈ ℓ`: with a large palette a list of size `ℓ` meets
  a random colour class of size `θΔ` in about `θΔ ℓ/c` colours only, so the
  palette-based estimate `|P|` is far too pessimistic there.


## Conventions

For a partial colouring `φ` of a subhypergraph `𝓗₀ ⊆ 𝓗` we write
`lostColours 𝓗₀ hsub φ L e` for the set of colours of `L e` that are *used at
some vertex of `e`*, i.e. that `e` can no longer use.  An uncoloured edge `e`
keeps the list `L e \ lostColours …`, whose size is at least
`|L e| - |lostColours …|`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ}

/-- The colours of `L e` that the partial colouring `φ` of `𝓗₀` has already
used at a vertex of `e`; the edge `e` cannot use them any more. -/
def lostColours {𝓗 : Hypergraph (Fin n)} (𝓗₀ : Hypergraph (Fin n))
    (_hsub : ∀ e ∈ 𝓗₀, e ∈ 𝓗) (φ : 𝓗₀.Coloring (Fin c)) (L : 𝓗 → Finset (Fin c))
    (e : 𝓗) : Finset (Fin c) := by
  classical
  exact (L e).filter fun γ =>
    ∃ v ∈ (e : Set (Fin n)), ∃ e' : 𝓗₀, v ∈ (e' : Set (Fin n)) ∧ φ.labels e' = γ

/-- **The one-round step of the nibble.**  For every `β > 0` and `r ≥ 2` there
are `0 < ψ < θ < 1` and `D₀ > 0` such that: for every linear hypergraph `𝓗` on
`Fin n` with `Δ(𝓗) ≤ D ≥ D₀`, all edges of size in `[2,r]`, and every list
assignment `L` with `|L e| ≥ (1+β)D`, there is a subhypergraph `𝓗₀ ⊆ 𝓗` and a
partial proper colouring `φ` of `𝓗₀` from the lists such that

* (progress) the maximum degree drops by the factor `(1-θ)`:
  `d_{𝓗∖𝓗₀}(v) ≤ (1-θ) Δ(𝓗)` for *every* vertex `v` (this is the form that is
  closed under iteration; it requires progress only at the vertices whose
  degree is close to `Δ(𝓗)`);
* (loss) every edge `e` not coloured in the round loses at most a `ψ`-fraction
  of its list: `|lostColours 𝓗₀ hsub φ L e| ≤ ψ (1+β) D`.
-/
def KahnRoundStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ r : ℕ, 2 ≤ r → ∃ θ ψ : ℝ,
    0 < ψ ∧ ψ < θ ∧ θ < 1 ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, 2 ≤ edgeSize (e : Set (Fin n))) →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, ∀ L : 𝓗 → Finset (Fin c),
        (∀ e : 𝓗, (1 + β) * D ≤ ((L e).card : ℝ)) →
      ∃ 𝓗₀ : Hypergraph (Fin n), ∃ hsub : ∀ e ∈ 𝓗₀, e ∈ 𝓗,
        ∃ φ : 𝓗₀.Coloring (Fin c),
          (∀ e : 𝓗₀, φ.labels e ∈ L ⟨(e : Set (Fin n)), hsub _ e.2⟩) ∧
          (∀ v : Fin n,
            ((hypergraphDegree (𝓗 \ 𝓗₀) v : ℕ) : ℝ) ≤
              (1 - θ) * ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ)) ∧
          (∀ e : 𝓗, (e : Set (Fin n)) ∉ 𝓗₀ →
            ((lostColours 𝓗₀ hsub φ L e).card : ℝ) ≤ ψ * ((1 + β) * D))

/-- Every colour lost by an uncoloured edge is a colour used by the round, hence
belongs to the round's palette. -/
theorem lostColours_subset_of_palette {𝓗 : Hypergraph (Fin n)} (𝓗₀ : Hypergraph (Fin n))
    (hsub : ∀ e ∈ 𝓗₀, e ∈ 𝓗) (φ : 𝓗₀.Coloring (Fin c)) (L : 𝓗 → Finset (Fin c))
    (P : Finset (Fin c)) (hφ : ∀ e : 𝓗₀, φ.labels e ∈ P) (e : 𝓗) :
    lostColours 𝓗₀ hsub φ L e ⊆ P := by
  classical
  intro γ hγ
  simp only [lostColours, Finset.mem_filter] at hγ
  obtain ⟨-, v, -, e', -, hlab⟩ := hγ
  rw [← hlab]
  exact hφ e'

end

end ErdosFaberLovaszConjecture
