import Submission.EFL.OptCol
import Submission.EFL.Counting
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Submission.Commons.Combinatorics.SimpleGraph.vizing
import Submission.Commons.Combinatorics.SimpleGraph.vizing_two_max

/-!
# The Glock–Kühn–Osthus machinery: definitions

This module sets up the vocabulary for Theorem 10.8 of Kang–Kelly–Kühn–Methuku–Osthus
(Theorem 1.6 of Glock–Kühn–Osthus, *Optimal path and cycle decompositions of dense
quasirandom graphs*), the optimal edge-colouring theorem for lower-regular graphs of even
order.

`ErdosFaberLovaszConjecture.GKOStatement` is phrased in the `Hypergraph` language (all
edges of size `2`) used by the EFL development.  Internally we work with
`SimpleGraph (Fin n)` (Mathlib's API plus the Vizing theorems of
`Submission.Commons.Combinatorics.SimpleGraph`), bridged through `graphOf`.

## Main definitions

* `Work.Deep.GKO.graphOf` — the simple graph underlying a 2-uniform hypergraph;
* `Work.Deep.GKO.crossEdges` — number of edges between two vertex sets;
* `Work.Deep.GKO.LowerReg` — lower `(p,ε)`-regularity, in graph language;
* `Work.Deep.GKO.robustNbrs`, `Work.Deep.GKO.RobustExpander` — robust expansion;
* `Work.Deep.GKO.IsPerfectMatching'`, `Work.Deep.GKO.HasOneFactorization`,
  `Work.Deep.GKO.HasHamiltonDecomposition`;
* `Work.Deep.GKO.KOStatement` — Kühn–Osthus for robustly expanding regular graphs;
* `Work.Deep.GKO.GKOStatementFixed` — the corrected form of Theorem 10.8.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The graph underlying a 2-uniform hypergraph -/

/-- The simple graph underlying a hypergraph all of whose edges have size `2`. -/
def graphOf (𝓖 : Hypergraph (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ({u, v} : Set (Fin n)) ∈ 𝓖
  symm := Std.Symm.mk (fun u v h => ⟨h.1.symm, by rw [Set.pair_comm]; exact h.2⟩)
  loopless := Std.Irrefl.mk (fun u h => h.1 rfl)

@[simp]
theorem graphOf_adj {𝓖 : Hypergraph (Fin n)} {u v : Fin n} :
    (graphOf 𝓖).Adj u v ↔ u ≠ v ∧ ({u, v} : Set (Fin n)) ∈ 𝓖 := Iff.rfl

/-! ## Numbers of edges between vertex sets -/

/-- The number of edges of `G` between the disjoint vertex sets `A` and `B`. -/
def crossEdges (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : ℕ := by
  classical
  exact ((A.product B).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card

/-- Lower `(p,ε)`-regularity of a graph on `n` vertices (one-sided `ε`-regularity). -/
def LowerReg (G : SimpleGraph (Fin n)) (p ε : ℝ) : Prop :=
  ∀ A B : Finset (Fin n), Disjoint A B → ε * (n : ℝ) ≤ (A.card : ℝ) →
    ε * (n : ℝ) ≤ (B.card : ℝ) →
    (p - ε) * (A.card : ℝ) * (B.card : ℝ) ≤ (crossEdges G A B : ℝ)

/-! ## Robust expansion -/

/-- The `ν`-robust neighbourhood of a vertex set: the vertices with at least `νn`
neighbours in `S`. -/
def robustNbrs (G : SimpleGraph (Fin n)) (ν : ℝ) (S : Finset (Fin n)) : Set (Fin n) :=
  {x | ν * (n : ℝ) ≤ ((G.neighborSet x ∩ (S : Set (Fin n))).ncard : ℝ)}

/-- **Robust expansion.**  `G` is a robust `(ν,τ)`-expander if every vertex set `S` with
`τn ≤ |S| ≤ (1-τ)n` has `ν`-robust neighbourhood of size at least `|S| + νn`. -/
def RobustExpander (G : SimpleGraph (Fin n)) (ν τ : ℝ) : Prop :=
  ∀ S : Finset (Fin n), τ * (n : ℝ) ≤ (S.card : ℝ) → (S.card : ℝ) ≤ (1 - τ) * (n : ℝ) →
    (S.card : ℝ) + ν * (n : ℝ) ≤ ((robustNbrs G ν S).ncard : ℝ)

/-! ## Matchings, Hamilton decompositions, 1-factorizations -/

/-- A perfect matching of `G`, as a spanning subgraph in which every vertex has degree one. -/
def IsPerfectMatching' (G M : SimpleGraph (Fin n)) : Prop :=
  M ≤ G ∧ ∀ v : Fin n, ∃! w : Fin n, M.Adj v w

/-- `H` **is** a Hamilton cycle: it contains a spanning cycle and is `2`-regular (so its edge
set is exactly that cycle).

Note that Mathlib's `SimpleGraph.IsHamiltonian H` only says that `H` *contains* a Hamilton
cycle; a Hamilton decomposition needs the parts to *be* Hamilton cycles, hence the extra
`2`-regularity conjunct. -/
def IsHamiltonCycle' (H : SimpleGraph (Fin n)) : Prop :=
  H.IsHamiltonian ∧ ∀ v : Fin n, Nat.card (H.neighborSet v) = 2

/-- **Hamilton decomposition.**  The edge set of `G` is partitioned into Hamilton cycles. -/
def HasHamiltonDecomposition (G : SimpleGraph (Fin n)) : Prop :=
  ∃ k : ℕ, ∃ C : Fin k → SimpleGraph (Fin n),
    (∀ i, C i ≤ G) ∧ (∀ i, IsHamiltonCycle' (C i)) ∧
    (∀ i j, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet) ∧
    (∀ e ∈ G.edgeSet, ∃ i, e ∈ (C i).edgeSet)

/-- A matching: no two edges of `M` share a vertex. -/
def IsMatching' (M : SimpleGraph (Fin n)) : Prop :=
  ∀ v w w' : Fin n, M.Adj v w → M.Adj v w' → w = w'

/-- **1-factorization with `k` factors.**  The edge set of `G` is partitioned into `k`
perfect matchings. -/
def HasOneFactorization (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ M : Fin k → SimpleGraph (Fin n),
    (∀ i, IsPerfectMatching' G (M i)) ∧
    (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) ∧
    (∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet)

/-- **Matching decomposition with `k` matchings.**  The edge set of `G` is partitioned into
`k` matchings; equivalently `G` has a proper edge colouring with `k` colours. -/
def HasMatchingDecomposition (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ M : Fin k → SimpleGraph (Fin n),
    (∀ i, IsMatching' (M i)) ∧ (∀ i, M i ≤ G) ∧
    (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) ∧
    (∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet)

/-- A linear forest: an acyclic graph of maximum degree at most `2`. -/
def IsLinearForest (F : SimpleGraph (Fin n)) : Prop :=
  F.IsAcyclic ∧ ∀ v : Fin n, Nat.card (F.neighborSet v) ≤ 2

/-- A spanning linear forest whose set of leaves (vertices of degree one) is exactly `L`.
Every vertex has degree one or two, so the forest is a disjoint union of paths, each of
length at least one, and the path endpoints are precisely the vertices of `L`. -/
def IsSpanningLinearForestWithLeaves (F : SimpleGraph (Fin n)) (L : Finset (Fin n)) : Prop :=
  F.IsAcyclic ∧ (∀ v : Fin n, 1 ≤ Nat.card (F.neighborSet v)) ∧
    (∀ v : Fin n, Nat.card (F.neighborSet v) ≤ 2) ∧
    (∀ v : Fin n, Nat.card (F.neighborSet v) = 1 ↔ v ∈ L)

/-- Maximum degree, in the `Nat.card`-of-neighbour-set form (no decidability needed). -/
def maxDeg (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup (fun v => Nat.card (G.neighborSet v))

/-- Minimum degree, in the `Nat.card`-of-neighbour-set form (no decidability needed). -/
def minDeg (G : SimpleGraph (Fin n)) : ℕ :=
  sInf (Set.range (fun v : Fin n => Nat.card (G.neighborSet v)))

/-- A graph is `r`-regular if every vertex has exactly `r` neighbours. -/
def IsRegularOf (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∀ v : Fin n, Nat.card (G.neighborSet v) = r

/-! ## The deep input: Kühn–Osthus for robustly expanding regular graphs -/

/-- The Kühn–Osthus result with an **explicit** robustness threshold `τ : ℝ → ℝ`, i.e. the
strengthening of `KOStatement` in which the robustness parameter of the hypothesis and the
range parameter are the *given* number `τ α` rather than an unspecified positive constant.

Kühn–Osthus prove their result by an argument that produces some explicit `τ`, so this is the
form a development needs in order to instantiate the theorem with concrete numerical margins
(the paper's own constants are only stated existentially).  With `τ` explicit, the reduction
yields Theorem 10.8 with the explicit hierarchy of `Work.Deep.GKO.GKOStatementExplicit`
(proved as `Work.Deep.GKO.gkoStatementExplicit_of_KOExplicit`):  at
`α := min (p/2) (1/10)`,
`ν ≤ min (α * p^2 * τ(α)^2 / 10^20) (α^3 / 10^20)` and `ε ≤ p * τ(α) * α / 10^20`.
The constants are not optimal (they are the ones the formalised reduction produces); they
are what a consumer must meet in order to instantiate Theorem 10.8 with concrete numbers. -/
def KOStatementExplicit (τ : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ ν : ℝ, 0 < ν → ν ≤ τ α → ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν (τ α) → ∀ r : ℕ,
      IsRegularOf G r → α * (n : ℝ) ≤ (r : ℝ) → Even r → HasHamiltonDecomposition G

/-! ## Theorem 10.8 with an explicit hierarchy -/

/-- **The explicit hierarchy of Theorem 10.8.**  With `α := min (p/2) (1/10)` the density at
which Kühn--Osthus is applied and `τ α` its robustness threshold, the discrepancy
`ν = Δ - δ` and the regularity parameter `ε` must satisfy

* `ν ≤ min (min (α * p^2 * (τ α)^2 / 14336) (α^3 / 2240000)) (α * p^2 / 2240000)`, and
* `ε ≤ min (min (p * (τ α) / 16) (α / 200)) (min (p / 200) ((τ α) / 2))`.

These are the constants *actually used* by the reduction in
`Work.Deep.GKO.gkoStatementTau_of_KOExplicit`: the earlier form of that file carried slack
factors `10^-20` in place of the five constants above, which made the hierarchy unusable for
concrete numerical margins (such as those of §12 of the paper, which needs
`τ(σ/16) ≳ 10^-12` rather than `τ(σ/16) ≳ 10^8/σ`).

The statement is *false* if no hierarchy is imposed (see
`Work.Deep.GKO.not_gkoStatementNoSmallness`). -/
def GKOExplicitHierarchy (τ : ℝ → ℝ) (ν ε p : ℝ) : Prop :=
  let α := min (p / 2) (1 / 10)
  ν ≤ min (min (α * p ^ 2 * (τ α) ^ 2 / 14336) (α ^ 3 / 2240000)) (α * p ^ 2 / 2240000) ∧
    ε ≤ min (min (p * (τ α) / 16) (α / 200)) (min (p / 200) ((τ α) / 2))

/-- **Theorem 10.8 of the paper with explicit thresholds.**  For a given function
`τ : ℝ → ℝ` (a robustness threshold supplied by a proof of Kühn--Osthus, in the sense of
`KOStatementExplicit`), the conclusion of Theorem 10.8 holds as soon as the explicit
hierarchy `GKOExplicitHierarchy τ ν ε p` holds.  This is the interface through which the
paper's existential thresholds become checkable numbers:
see `Work.Deep.GKO.gkoStatementExplicit_of_KOExplicit`.

(The pre-repair `ErdosFaberLovaszConjecture.GKOStatement` imposes the *linear* hierarchy
`10^10 * (ν+ε) ≤ p` instead, which for small `p` allows `ν ≈ p/10^10` while the reduction from
Kühn--Osthus needs `ν ≲ p^3`: see `Work.Deep.GKO.linearHierarchy_not_explicitHierarchy`.
The linear form is therefore not a consequence of `KOStatement`; it is a strictly stronger
statement, of unknown truth value.) -/
def GKOStatementExplicit (τ : ℝ → ℝ) : Prop :=
  ∀ ν ε p : ℝ, 0 < ν → 0 < ε → ε < p → p < 1 → GKOExplicitHierarchy τ ν ε p →
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
      (∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) →
      ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
        (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ)) ≤ ν * (n : ℝ)) →
      Even n →
      (∃ w : Fin n, (∀ v : Fin n, ErdosFaberLovaszConjecture.degAt 𝓖 w ≤
          ErdosFaberLovaszConjecture.degAt 𝓖 v) ∧
        ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
            (ErdosFaberLovaszConjecture.degAt 𝓖 w : ℝ)) ≤
          ∑ v ∈ (Finset.univ.erase w),
            ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
              (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ))) →
      ErdosFaberLovaszConjecture.Hypergraph.Colorable
        (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖) 𝓖

/-- The **pre-repair** form of `ErdosFaberLovaszConjecture.GKOStatement`: identical to
`GKOStatementFixed`'s body but with `ν, ε` quantified *before* `N₀` and **no** smallness
relation with `p`.  This statement is false (`Work.Deep.GKO.not_gkoStatementNoSmallness`):
for `ε > 1/2` its lower-regularity hypothesis is vacuous, and the triangle plus isolated
vertices refutes it. -/
def GKOStatementNoSmallness : Prop :=
  ∀ ν ε p : ℝ, 0 < ν → 0 < ε → ε < p → p < 1 → ∃ N₀ : ℕ,
    ∀ n ≥ N₀, ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
      (∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) →
      ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
        (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ)) ≤ ν * (n : ℝ)) →
      Even n →
      (∃ w : Fin n, (∀ v : Fin n, ErdosFaberLovaszConjecture.degAt 𝓖 w ≤
          ErdosFaberLovaszConjecture.degAt 𝓖 v) ∧
        ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
            (ErdosFaberLovaszConjecture.degAt 𝓖 w : ℝ)) ≤
          ∑ v ∈ (Finset.univ.erase w),
            ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
              (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ))) →
      ErdosFaberLovaszConjecture.Hypergraph.Colorable
        (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖) 𝓖

/-- **Kühn–Osthus** (*Hamilton decompositions of regular expanders*, Adv. Math. 237 (2013);
undirected form from JCTB 104 (2014)): for every `α > 0` there is `τ > 0` such that every
`r`-regular robust `(ν,τ)`-expander on `n` vertices with `r ≥ αn` and `r` even has a Hamilton
decomposition. -/
def KOStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν τ → ∀ r : ℕ,
      IsRegularOf G r → α * (n : ℝ) ≤ (r : ℝ) → Even r → HasHamiltonDecomposition G

/-! ## The corrected form of Theorem 10.8 -/

/-- **Theorem 10.8 of the paper (Glock–Kühn–Osthus), corrected.**  For each `p ∈ (0,1)`
there are thresholds `ν₀, ε₀ > 0` such that for all `0 < ν ≤ ν₀`, `0 < ε ≤ ε₀`, large even
`n`, and every 2-uniform hypergraph `𝓖` on `Fin n` that is lower `(p,ε)`-regular with
`Δ - δ ≤ νn` and such that some minimum-degree vertex `w` satisfies the paper's `(def_ineq)`
condition, `χ'(𝓖) = Δ(𝓖)`.

The thresholds are existential because the paper's hypothesis is `0 < 1/n₀ ≪ ν, ε ≪ p < 1`.
The version in which `ν` and `ε` are quantified before `N₀` is *false*: see
`Work.Deep.GKO.not_gkoStatementNoSmallness`. -/
def GKOStatementFixed : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∃ ν₀ ε₀ : ℝ, 0 < ν₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
    (∀ ν ε : ℝ, 0 < ν → ν ≤ ν₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
      ∀ n ≥ N₀, ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
      SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ ν * (n : ℝ)) →
      Even n →
      (∃ w : Fin n, (∀ v : Fin n, degAt 𝓖 w ≤ degAt 𝓖 v) ∧
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
          ∑ v ∈ (Finset.univ.erase w),
            ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖))

end

end Work.Deep.GKO
