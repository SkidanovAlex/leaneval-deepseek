import Submission.EFL.Matching
import Submission.EFL.Counting
import Submission.EFL.EdgeSize
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# The "large-edge theorem" (Theorem 6.7 / `large-edge-thm` of the paper)

This file states, on the exact `ChallengeDeps` definitions, the central
intermediate theorem used to colour the *medium and large* edges of the
hypergraph in §12 (and to prove Theorems 1.2 and 1.3 in §6):

> **Theorem (large-edge-thm).** Let
> `0 < 1/n₀ ≪ 1/r₀ ≪ 1/r₁, β ≪ γ₁ ≪ σ ≪ δ ≪ γ₂ ≪ 1` and let `n ≥ n₀`.
> If `𝓗` is an `n`-vertex linear hypergraph in which every edge has size
> `> r₁`, then at least one of the following holds.
>
> **(a)** [non-extremal] there is a proper edge-colouring of `𝓗` with at most
> `(1−σ)n` colours such that
>   (i) a colour assigned to a *huge* edge is assigned to no other edge;
>   (ii) every *medium* edge is assigned a colour from a set `C_med` of size
>        at most `γ₁n`, and each colour in `C_med` is incident with at most
>        `γ₁n` vertices;
>   (iii) every colour outside `C_med` that is not assigned to a huge edge is
>        incident with at most `βn` vertices.
>
> **(b)** [extremal] there is a set of *FPP-extremal* edges of volume at least
> `1 − δ`, and a proper edge-colouring of `𝓗` with at most `n` colours such
> that
>   (i) a colour assigned to a huge edge is incident with at most `δn`
>       vertices;
>   (ii) every medium edge is assigned a colour from a set `C_med` of size at
>        most `γ₂n`, and each colour in `C_med` is incident with at most
>        `γ₁n` vertices;
>   (iii) every colour outside `C_med` that is not assigned to a huge edge is
>        incident with at most `βn` vertices.

Here *huge* = size ≥ `βn/4`, *medium* = `r₁ < size ≤ r₀`, and *FPP-extremal*
= size within `δ√n` of `√n` (Definition `def:edgesize`), and the *volume* of
a set `W` of edges is `(∑_{e∈W} C(|e|,2)) / C(n,2)`.

The theorem is parameterized by the real constants `β γ₁ σ δ γ₂` and the
thresholds `r₁ r₀ n₀`; the `≪` hierarchy means that the result holds whenever
the parameters are chosen from right to left sufficiently small (the paper's
convention, §Notation).  In `LargeEdgeInstance` below we record the
per-instance implication (for a fixed choice of all parameters and thresholds)
that the hierarchy has to deliver; the hierarchy itself (`∀ γ₂ ∃ δ₀ ∀ δ ≤ δ₀
∃ σ₀ ...`) is a straightforward nested `∃`-form that the eventual proof must
establish, recorded in the doc comment.  All quantities on colour classes use
the colour host `Fin n`; colour classes outside a declared colour set are
empty, so "uses colour set `C₁`" (range contained in `C₁`) with `|C₁| ≤ m`
is exactly "colouring with at most `m` colours".

## Proof decomposition of Theorem 6.7 (paper §6–§7), for the road ahead

The proof splits according to the Reordering lemma (`reordering-lemma`, §7):

1. **Reordering lemma.** For `0 < 1/r₁ ≪ τ, 1/K` with `1 − τ − 7τ^{1/4}/K > 0`,
   a linear `n`-vertex `𝓗` with all `|e| ≥ r₁` admits an ordering of its edges
   such that either (good) every `fwddeg(e) ≤ (1−τ)n`, or there is a set
   `W ∋ e*` with `max_W |e| ≤ (1+3τ^{1/4}K⁴) min_W |e|` and
   `vol(W) ≥ (1 − τ − 7τ^{1/4}/K)² / (1 + 3τ^{1/4}K⁴)`; in the second case the
   ordering is size-monotone up to `e*` and all edges after `e*` are good.
   The proof needs propositions `fwdnbr-prop` (bounds on forward degrees and
   neighbourhood counts by edge size) which are pure counting over pairs.
2. **Few large colour classes** (`few-large-colour-classes-prop`): if
   `M₁,…,M_t` are pairwise edge-disjoint matchings each covering ≥ `αn`
   vertices then `t ≤ n/(αr)` (uses the pair-counting in `Counting.lean`);
   and an `α`-bounded colouring with `χ'(𝓗) + 2n/(α²r)` colours exists.
3. **Greedy colouring** (`greedy-colouring-prop`) over an ordering produced by
   the Reordering lemma, giving the colour classes of case (a)/(b).
4. **Local sparsity** (externals): Molloy–Reed `local-sparsity-lemma` and
   Alon–Krivelevich–Sudakov `aks-local-sparsity`, applied to induced parts of
   the line graph (the colour class sizes need `SimpleGraph` machinery on
   `lineGraph 𝓗`), colouring the "hard" edge set `W` cheaply.
5. **Extremal regime** (`fpp-extremal-section`, §6): `extremal-case-lemma`,
   the FPP-extremal proposition, and the "nearly all pairs covered" argument
   giving case (b), including the `W₁/W₂` split proposition (§7, p. 1077) and
   the internal claims; needs the volume bound `vol(𝓗) ≤ 1` (from
   `Counting.sum_edgeSize_mul_sub_le`) and the matching machinery of §5
   (Ehard–Glock–Joos, Chernoff).
6. **Assembly** (§7, "Proof of Theorems 1.2 and 6.7"): combine the two
   regimes and verify properties (i)–(iii) of the chosen alternative.

## Definitions formalised here

Colour-class vocabulary (vertices incident with a colour class; coverage
bounds, in naturals and reals; "uses colour set"), edge-size predicates, the
non-extremal and extremal colouring properties, extremal volume, and the
per-instance theorem statement `LargeEdgeInstance`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The vertices incident with the edges of the colour class `c` of a
colouring `φ` of `𝓗` (i.e. `V(φ⁻¹(c))`). -/
def Hypergraph.Coloring.classVertices {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n)) (c : Fin n) :
    Set (Fin n) :=
  {v : Fin n | ∃ e : 𝓗, e ∈ φ.colorClass c ∧ v ∈ (e : Set (Fin n))}

/-- Membership in the set of vertices incident with a colour class. -/
theorem mem_classVertices {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n)) (c : Fin n)
    (v : Fin n) : v ∈ φ.classVertices c ↔ ∃ e : 𝓗, e ∈ φ.colorClass c ∧ v ∈ (e : Set (Fin n)) := by
  rfl

/-- The number of vertices incident with an edge coloured `c` by `φ`. -/
def Hypergraph.Coloring.classVertexCount {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n)) (c : Fin n) :
    ℕ :=
  (φ.classVertices c).ncard

/-- The colour class `c` is incident with at most `b` vertices (natural bound). -/
def Hypergraph.Coloring.classCoversVertices {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n)) (c : Fin n)
    (b : ℕ) : Prop :=
  φ.classVertexCount c ≤ b

/-- The colour class `c` is incident with at most `α` vertices (real bound,
used for bounds like `βn`, `γ₁n`). -/
def Hypergraph.Coloring.classCoversVerticesOf {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n)) (c : Fin n)
    (α : ℝ) : Prop :=
  (φ.classVertexCount c : ℝ) ≤ α

/-- A colour class covers at most `n` vertices (all colour classes lie inside
the vertex set `Fin n`). -/
theorem classVertexCount_le_n {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n)) (c : Fin n) :
    φ.classVertexCount c ≤ n := by
  have hsub : φ.classVertices c ⊆ (Set.univ : Set (Fin n)) := by
    intro v _hv
    trivial
  exact (Set.ncard_le_ncard hsub).trans (by simp)

/-- The colouring `φ` uses only colours from the colour set `C`. -/
def Hypergraph.Coloring.UsesColourSet {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n))
    (C : Finset (Fin n)) : Prop :=
  ∀ e : 𝓗, φ.labels e ∈ C

/-- Using a smaller colour set is a stronger property. -/
theorem UsesColourSet_mono {𝓗 : Hypergraph (Fin n)} {φ : 𝓗.Coloring (Fin n)}
    {C C' : Finset (Fin n)} (hCC' : C ⊆ C') (hφ : φ.UsesColourSet C) : φ.UsesColourSet C' := by
  intro e
  exact hCC' (hφ e)

/-- The colour `c` is *assigned to a huge edge* by `φ` (some edge coloured `c`
has size at least `βn/4`). -/
def Hypergraph.Coloring.AssignedToHuge {𝓗 : Hypergraph (Fin n)} (β : ℝ) (φ : 𝓗.Coloring (Fin n))
    (c : Fin n) : Prop :=
  ∃ e : 𝓗, e ∈ φ.colorClass c ∧ β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)

/-- Colour classes that contain a huge edge are singletons (property (i) of
the non-extremal alternative). -/
def Hypergraph.Coloring.SingletonClassesForHuge {𝓗 : Hypergraph (Fin n)} (β : ℝ)
    (φ : 𝓗.Coloring (Fin n)) : Prop :=
  ∀ c : Fin n, φ.AssignedToHuge β c → ∃ e₀ : 𝓗, φ.colorClass c = {e₀}

/-- An edge is *huge* if its size is at least `βn/4`. -/
def edgeHuge (β : ℝ) (n : ℕ) (e : Set (Fin n)) : Prop :=
  β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ)

/-- An edge is *medium* if `r₁ < |e| ≤ r₀`. -/
def edgeMedium (r₁ r₀ : ℝ) (e : Set (Fin n)) : Prop :=
  (r₁ : ℝ) < (edgeSize e : ℝ) ∧ (edgeSize e : ℝ) ≤ (r₀ : ℝ)

/-- An edge is *FPP-extremal* if its size is within `δ√n` of `√n`. -/
def edgeExtremal (δ : ℝ) (n : ℕ) (e : Set (Fin n)) : Prop :=
  (1 - δ) * Real.sqrt n ≤ (edgeSize e : ℝ) ∧ (edgeSize e : ℝ) ≤ (1 + δ) * Real.sqrt n

/-- An edge is huge iff it belongs to the hypergraph `𝓗.hugeEdges` when it is
an edge of `𝓗`. -/
theorem edgeHuge_iff_mem_hugeEdges {𝓗 : Hypergraph (Fin n)} (β : ℝ) (e : Set (Fin n))
    (he : e ∈ 𝓗) : edgeHuge β n e ↔ e ∈ 𝓗.hugeEdges β := by
  simp [edgeHuge, he]

/-- The *volume* of a hypergraph `𝓗` on `Fin n`:
`vol(𝓗) = (∑_e |e|(|e|−1)) / (n(n−1)) = ∑_e C(|e|,2) / C(n,2)`.  Defined for
every (finite) hypergraph on `Fin n`; the paper only uses it when `n` is
large and `𝓗` is linear, in which case `vol(𝓗) ≤ 1`. -/
def volume (n : ℕ) (𝓗 : Hypergraph (Fin n)) : ℝ := by
  classical
  let E : Finset (Set (Fin n)) :=
    (Finset.univ : Finset (Set (Fin n))).filter (fun e : Set (Fin n) => e ∈ 𝓗)
  exact (((E.sum fun e : Set (Fin n) => (edgeSize e) * (edgeSize e - 1)) : ℕ) : ℝ) /
    (((n : ℝ) * ((n - 1 : ℕ) : ℝ)))

/-- If `𝓗` is linear then its volume is at most `1`
(`vol(𝓗) = ∑_e C(|e|,2) / C(n,2) ≤ 1`, since distinct pairs of vertices lie
in at most one edge). -/
theorem volume_le_one_of_linear {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) :
    volume n 𝓗 ≤ 1 := by
  classical
  let E : Finset (Set (Fin n)) :=
    (Finset.univ : Finset (Set (Fin n))).filter (fun e : Set (Fin n) => e ∈ 𝓗)
  have hsub : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ E → e₂ ∈ E → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton := by
    intro e₁ e₂ he₁ he₂ hne
    exact hlin (Finset.mem_filter.mp he₁).2 (Finset.mem_filter.mp he₂).2 hne
  have hnat : E.sum (fun e : Set (Fin n) => (edgeSize e) * (edgeSize e - 1)) ≤ n * (n - 1) :=
    sum_edgeSize_mul_sub_le_on E hsub
  dsimp [volume]
  by_cases hden : ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) = 0
  · rw [hden]
    simp
  · have hdenpos : 0 < ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
      have hn2 : 2 ≤ n := by
        by_contra hn
        have hnle : n ≤ 1 := by omega
        interval_cases n <;> simp at hden
      positivity
    rw [div_le_one₀ hdenpos]
    exact_mod_cast hnat

/-- The extremal case (b) of Theorem 6.7: a set of FPP-extremal edges of
volume at least `1 − δ`, and a colouring satisfying (i)–(iii). -/
def LargeEdgeExtremal (n : ℕ) (δ γ₂ γ₁ β : ℝ) (r₁ r₀ : ℝ)
    (𝓗 : Hypergraph (Fin n)) : Prop :=
  (∃ W : Hypergraph (Fin n), W ⊆ 𝓗 ∧ (∀ e : Set (Fin n), e ∈ W → edgeExtremal δ n e) ∧
      1 - δ ≤ volume n W) ∧
  ∃ (φ : 𝓗.Coloring (Fin n)) (Cmed : Finset (Fin n)),
    (Cmed.card : ℝ) ≤ γ₂ * (n : ℝ) ∧
    (∀ e : 𝓗, edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed) ∧
    (∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) ∧
    (∀ c : Fin n, φ.AssignedToHuge β c → (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ)) ∧
    (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c → (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))

/-- The non-extremal case (a) of Theorem 6.7: a colouring with at most
`(1−σ)n` colours satisfying (i)–(iii). -/
def LargeEdgeNonExtremal (n : ℕ) (σ γ₁ β : ℝ) (r₁ r₀ : ℝ)
    (𝓗 : Hypergraph (Fin n)) : Prop :=
  ∃ (φ : 𝓗.Coloring (Fin n)) (C₁ Cmed : Finset (Fin n)),
    φ.UsesColourSet C₁ ∧
    (C₁.card : ℝ) ≤ (1 - σ) * (n : ℝ) ∧
    Cmed ⊆ C₁ ∧
    (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ) ∧
    (∀ e : 𝓗, edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed) ∧
    (∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) ∧
    φ.SingletonClassesForHuge β ∧
    (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c → (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))

/-- The per-instance content of Theorem 6.7 (`large-edge-thm`) for a *fixed*
choice of parameters and thresholds: the statement the `≪`-hierarchy must
deliver for every admissible tuple.  (`IsLinear` and the lower bound
`r₁ < |e|` on every edge are the theorem's hypotheses; the alternatives are
`LargeEdgeNonExtremal` (a) and `LargeEdgeExtremal` (b).) -/
def LargeEdgeInstance (n n₀ : ℕ) (r₁ r₀ : ℝ) (β γ₁ σ δ γ₂ : ℝ)
    (𝓗 : Hypergraph (Fin n)) : Prop :=
  (n₀ : ℝ) ≤ n → (∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ)) →
    𝓗.IsLinear →
      LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ 𝓗 ∨ LargeEdgeExtremal n δ γ₂ γ₁ β r₁ r₀ 𝓗

/-- Theorem 6.7 (`large-edge-thm`) at the level of thresholds: for every
`γ₂ ∈ (0,1]` there is `δ₀ ≤ γ₂` such that for all `0 < δ ≤ δ₀` there is
`σ₀ ≤ δ` such that for all `0 < σ ≤ σ₀` there is `γ₁₀ ≤ σ` such that for all
`0 < γ₁ ≤ γ₁₀` there is `β₀ ≤ γ₁` such that for all `0 < β ≤ β₀` integer thresholds
`R₁` (depending on `β`), then `R₀` (depending on `r₁`), then `N₀` (depending
on `r₀`), such that for all `r₁ ≥ R₁`, `r₀ ≥ R₀`, `n ≥ N₀` and every
`n`-vertex linear hypergraph `𝓗` whose edges all have size `> r₁`, the
instance `LargeEdgeInstance` holds.  (This is the nested
`∃`-reading of the hierarchy `0 < 1/n₀ ≪ 1/r₀ ≪ 1/r₁, β ≪ γ₁ ≪ σ ≪ δ ≪
γ₂ ≪ 1`.) -/
def LargeEdgeThmStatement : Prop :=
  ∀ (γ₂ : ℝ), 0 < γ₂ → γ₂ ≤ 1 →
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ γ₂ ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∃ (σ₀ : ℝ), 0 < σ₀ ∧ σ₀ ≤ δ ∧
          ∀ (σ : ℝ), 0 < σ → σ ≤ σ₀ →
            ∃ (γ₁₀ : ℝ), 0 < γ₁₀ ∧ γ₁₀ ≤ σ ∧
              ∀ (γ₁ : ℝ), 0 < γ₁ → γ₁ ≤ γ₁₀ →
                ∃ (β₀ : ℝ), 0 < β₀ ∧ β₀ ≤ γ₁ ∧
                  ∀ (β : ℝ), 0 < β → β ≤ β₀ →
                    ∃ (R₁ : ℕ), 0 < R₁ ∧
                      ∀ (r₁ : ℕ), R₁ ≤ r₁ →
                        ∃ (R₀ : ℕ), 0 < R₀ ∧
                          ∀ (r₀ : ℕ), R₀ ≤ r₀ →
                            ∃ (N₀ : ℕ), 0 < N₀ ∧
                              ∀ (n : ℕ), N₀ ≤ n →
                                ∀ (𝓗 : Hypergraph (Fin n)),
                                  (∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ)) →
                                    𝓗.IsLinear →
                                      LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 ∨
                                      LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗

end
