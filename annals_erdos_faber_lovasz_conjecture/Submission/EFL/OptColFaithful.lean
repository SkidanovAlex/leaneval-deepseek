import Submission.EFL.OptCol
import Submission.Work.S12Faithful.Cone

/-!
# The faithful form of Corollary 10.13 (`cor:optcol`), cone side

`ErdosFaberLovaszConjecture.GKOStatement` (`Submission/EFL/OptCol.lean`) is the *faithful*
existential-threshold form of Theorem 10.8, with thresholds `ν₀(p), ε₀(p)` depending on the
density `p`.  This module records the corresponding form of Corollary 10.13 as
`ErdosFaberLovaszConjecture.optcol_corollary`: for every `p ∈ (0,1)` there are `η₀, ε₀ > 0`
with `ε₀ ≤ p` such that the conclusion holds for all `η ≤ η₀`, `ε ≤ ε₀`.

It is `Work.S12Faithful.optcol_corollary_faithful`, i.e. the `GKO` chapter's
`corollary_10_13_from_fixed` applied to `Work.Deep.GKO.GKOStatementFixed` (definitionally the
same Prop as `GKOStatement`).

**Why this module and not `OptColOdd.lean`.**  The odd-case reduction of the chapter
(`Submission/Work/Deep/GKO/corollary_10_13_odd_from_fixed.lean`) imports
`Submission.EFL.OptColOdd`, so the `GKO` chapter lies *downstream* of `OptColOdd` and
`OptColOdd` cannot import it.  Since `OptColFaithful` is downstream of both, it is the first
cone module in which the faithful corollary can be stated.

`Submission/EFL/OptColOdd.lean` continues to hold the *conditional* lemmas
`optcol_corollary_core`/`optcol_corollary_even`/`optcol_corollary_odd`, which are proved from
the stronger linear-hierarchy input `GKOStatementLinear`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Corollary 10.13 (`cor:optcol`)**, both parities, in the faithful form. -/
theorem optcol_corollary (hGKO : GKOStatement) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀ : ℝ, 0 < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, ∀ 𝓖 : Hypergraph (Fin n),
          (∀ e ∈ 𝓖, edgeSize e = 2) → SelfLowerRegular 𝓖 Set.univ p ε →
          (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
          (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
            (hypergraphMaxDegree 𝓖 : ℝ)) →
          𝓖.Colorable (hypergraphMaxDegree 𝓖)) :=
  Work.S12Faithful.optcol_corollary_faithful hGKO

end

end ErdosFaberLovaszConjecture
