import Submission.Work.Deep.GKO.Deliverable

/-!
# The cone-side switch, ready to paste (deliverable item 3)

The cone (`Submission/EFL/OptCol.lean:70`) currently defines

```
def GKOStatement : Prop := ∀ ν ε p, … 10 ^ 10 * (ν + ε) ≤ p → … ∃ N₀, ∀ n ≥ N₀, …
```

i.e. Theorem 10.8 with a *linear* hierarchy, which is stronger than what the Kühn–Osthus
proof yields (see the SESSION-4 warning in `OptCol.lean` and `NOTES_LEAD_GKO.md`).  The
lead's route (3) replaces it by the faithful existential-threshold form, which is
`Work.Deep.GKO.GKOStatementFixed`.  This module holds the two items of the switch that are
*not* cone edits, so that the lead's edit is a paste:

* `Work.S12Faithful.GKOStatementFaithful` — the faithful statement, as an `abbrev` of
  `Work.Deep.GKO.GKOStatementFixed`;
* `Work.S12Faithful.optcol_corollary_faithful` — Corollary 10.13 (both parities) with
  existential thresholds, i.e. the faithful replacement of
  `ErdosFaberLovaszConjecture.optcol_corollary`, obtained from
  `Work.Deep.GKO.corollary_10_13_from_fixed`.

`NOTES.md` (same directory) records the exact edits in `Submission/EFL/OptCol.lean`,
`S12A2Main.lean` and `Submission.lean`.  Nothing here edits a cone file.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.S12Faithful

open ErdosFaberLovaszConjecture

/-- The faithful (existential-threshold) form of Theorem 10.8 of the paper: the shape the
cone's `GKOStatement` takes after the switch. -/
abbrev GKOStatementFaithful : Prop := Work.Deep.GKO.GKOStatementFixed

/-- **Corollary 10.13 (`cor:optcol`) with existential thresholds.**  For every `p ∈ (0,1)`
there are `η₀, ε₀ > 0` with `ε₀ ≤ p` such that every `2`-uniform `𝓖` on `Fin n` that is
lower `(p,ε)`-regular with `ε ≤ ε₀`, has degree spread `Δ - d(v) ≤ ηn` with `η ≤ η₀`, and
at least `Δ(𝓖)` vertices of degree below `Δ(𝓖)`, is `Δ(𝓖)`-edge-colourable, for all
sufficiently large `n`.  This is the faithful replacement of
`ErdosFaberLovaszConjecture.optcol_corollary`. -/
theorem optcol_corollary_faithful (hGKO : GKOStatementFaithful) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀ : ℝ, 0 < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
        SelfLowerRegular 𝓖 Set.univ p ε →
        (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
        (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
          (hypergraphMaxDegree 𝓖 : ℝ)) →
        𝓖.Colorable (hypergraphMaxDegree 𝓖)) :=
  Work.Deep.GKO.corollary_10_13_from_fixed hGKO

end Work.S12Faithful
