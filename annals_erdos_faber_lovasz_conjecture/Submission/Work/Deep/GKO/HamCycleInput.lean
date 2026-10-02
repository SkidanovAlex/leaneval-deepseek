import Submission.Work.Deep.GKO.Defs

/-!
# The engine of the KO spine: Hamilton cycles in robust expanders

Both deep inputs of this chapter — `Work.Deep.GKO.ApproxHamDecompStatement` (Osthus–Staden's
approximate Hamilton decomposition) and `Work.Deep.GKO.AbsorptionStatement` (Kühn–Osthus'
robust decomposition) — are proved in the literature from one and the same engine:

> a robustly expanding graph of linear minimum degree contains a Hamilton cycle.

That engine is `HamCycleStatement` below (the undirected form of Theorem 16 of
Kühn–Osthus–Treglown, *Hamiltonian degree sequences in digraphs*, JCTB 100 (2010), 367–380,
which is the form in which Kühn–Osthus cite it; the LaTeX source is in `_papers/kot_clean.tex`,
their Theorem 4.1 / `expanderthm`, and Kühn–Osthus' *applications* paper derives the undirected
statement from the digraph one via their Lemma `orientexp`).

## Routes to the engine

Kühn–Osthus–Treglown's own proof (KOT §4) is *not* a pure rotation argument; it goes through
Szemerédi's regularity lemma:

1. apply the regularity lemma to `G` to obtain clusters `V₁,…,V_k` and an exceptional set `V₀`;
2. pass to the *reduced graph* `R` on the clusters and prove that `R` is again a robust
   expander with linear minimum degree (their Lemma `robustR`, with `robustG` for the passage
   from a degree condition to robust expansion);
3. thin `R` to a spanning subgraph `R*` which is still a robust expander and whose edges have
   density `≥ η/4` in `G` (their Lemma `orientexp`);
4. delete the "useless" vertices (those with few neighbours into the relevant clusters) into the
   exceptional set, so that every remaining vertex has linear degree in the graph `G*`
   corresponding to `R*`;
5. re-attach the exceptional vertices by hand (giving each of them `ηn/2` out- and inneighbours)
   and apply their blow-up cycle lemma (`cyclelemma`) to find a Hamilton cycle in `G*`.

The ingredient that had been missing from this workspace is now available in Mathlib:
**`SimpleGraph.szemeredi_regularity`** (`Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean`)
proves the effective equipartition form of Szemerédi's regularity lemma, together with the
uniformity machinery (`SimpleGraph.IsUniform`, `Finpartition.IsUniform`,
`Mathlib/Combinatorics/SimpleGraph/Regularity/{Uniform,Energy,Bound,Increment,Chunk,Equitabilise}.lean`).
So the remaining work for the engine is the *cluster-level* argument (steps 2–5) on top of a
regularity partition, not the regularity lemma itself.

## Consequences recorded here

* `Work.Deep.GKO.exists_hamiltonCycle_of_regular_of_hamCycle` — the regular case of the engine,
  which is the form used by the applications (`reggraphorient`, `ApproxHamDecompStatement`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

noncomputable section

/-! ## The engine -/

/-- **A robust expander of linear minimum degree contains a Hamilton cycle**
(Kühn–Osthus–Treglown).  For every `α > 0` there is a robustness threshold `τ > 0` such that
every robust `(ν,τ)`-expander (`ν ≤ τ`) on `n ≥ n₀` vertices whose degrees are all at least
`α n` has a Hamilton cycle. -/
def HamCycleStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν τ →
      (∀ v : Fin n, α * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ)) →
      ∃ C : SimpleGraph (Fin n), C ≤ G ∧ IsHamiltonCycle' C

/-- The regular case of the engine, in the form used by the applications: a regular robust
expander of linear degree contains a Hamilton cycle. -/
theorem exists_hamiltonCycle_of_regular_of_hamCycle (h : HamCycleStatement) {α : ℝ} (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν τ → ∀ r : ℕ, IsRegularOf G r →
        α * (n : ℝ) ≤ (r : ℝ) → ∃ C : SimpleGraph (Fin n), C ≤ G ∧ IsHamiltonCycle' C := by
  obtain ⟨τ, hτpos, h'⟩ := h α hα
  refine ⟨τ, hτpos, ?_⟩
  intro ν hν hντ
  obtain ⟨n₀, h₀⟩ := h' ν hν hντ
  refine ⟨n₀, ?_⟩
  intro n hn G hG r hr hrn
  refine h₀ n hn G hG ?_
  intro v
  rw [hr v]
  exact hrn

end

end Work.Deep.GKO
