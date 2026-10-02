import Submission.Work.Deep.GKO.Deliverable
import Submission.Work.Deep.GKO.QuantitativeInput

/-!
# The bridge to the cone's `GKOStatement`

Since 2026-09-23 (the CONE SWITCH, recorded next to `ErdosFaberLovaszConjecture.GKOStatement` in
`Submission/EFL/OptCol.lean`) the cone's `GKOStatement` is the *faithful* form of Theorem 10.8 —
the same body as this chapter's `Work.Deep.GKO.GKOStatementFixed`, so the two `Prop`s are
definitionally equal.  This module hands the requester exactly that `Prop`:

* `Work.Deep.GKO.gkoStatement_of_fixed : GKOStatementFixed → ErdosFaberLovaszConjecture.GKOStatement`;
* `Work.Deep.GKO.gkoStatement_of_approx_and_absorption` — the same, from the chapter's two deep
  tools (Osthus–Staden's approximate Hamilton decomposition and Kühn–Osthus' robust decomposition
  lemma), i.e. the exact shape in which the cone's input is now discharged;
* `Work.Deep.GKO.corollary_10_13_of_deepTools` — Corollary 10.13 of the paper from the same two
  tools.

The engine `Work.Deep.GKO.HamCycleStatement` enters both tools (it is the content of
`ApproxHamDecompStatement` and of `AbsorptionStatement`), and is itself reduced in this chapter to
`ClusterReductionStatement` and `FindCycleStatement` by the *proved*
`Work.Deep.GKO.hamCycleStatement_of_clusterReduction_and_findCycle`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

/-- The cone's `GKOStatement` is the faithful form of Theorem 10.8; this chapter's
`GKOStatementFixed` has the same body, so the two are interchangeable. -/
theorem gkoStatement_of_fixed (h : GKOStatementFixed) : ErdosFaberLovaszConjecture.GKOStatement := h

/-- **Theorem 10.8 of the paper, as the cone states it**, from the two deep tools of the
Kühn–Osthus line. -/
theorem gkoStatement_of_approx_and_absorption (hApp : ApproxHamDecompStatement)
    (hAbs : AbsorptionStatement) : ErdosFaberLovaszConjecture.GKOStatement :=
  gkoStatement_of_fixed (gkoStatementFixed_of_approx_and_absorption hApp hAbs)

/-- **Corollary 10.13 of the paper** (the input of §12), from the two deep tools, in the faithful
(threshold-existential) form. -/
theorem corollary_10_13_of_deepTools (hApp : ApproxHamDecompStatement)
    (hAbs : AbsorptionStatement) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀ : ℝ, 0 < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
        (∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) →
        ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε →
        (∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
          (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
        (({v : Fin n | ErdosFaberLovaszConjecture.degAt 𝓖 v <
          ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
          (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ)) →
        𝓖.Colorable (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖)) :=
  corollary_10_13_of_approx_and_absorption hApp hAbs

end

end Work.Deep.GKO
