import Submission.Work.Deep.GKO.KOInputs
import Submission.Work.Deep.GKO.gkoStatementFixed_of_KO
import Submission.Work.Deep.GKO.corollary_10_13_odd_from_fixed

/-!
# The GKO chapter's deliverable: Theorem 10.8 from the two deep tools

The chapter's target (per `NOTES_LEAD_GKO.md`) is `Work.Deep.GKO.GKOStatementFixed`, the
faithful existential-threshold form of Theorem 10.8 of Kang–Kelly–Kühn–Methuku–Osthus.  The
whole chapter is assembled into the two theorems below:

* `Work.Deep.GKO.gkoStatementFixed_of_approx_and_absorption` — Theorem 10.8 from Kühn–Osthus'
  two tools, `ApproxHamDecompStatement` (the approximate Hamilton decomposition, Osthus–Staden)
  and `AbsorptionStatement` (the robust decomposition / absorbing structure, KO Lemma 11.2);
* `Work.Deep.GKO.corollary_10_13_of_approx_and_absorption` — the paper's Corollary 10.13
  (`cor:optcol`, both parities) from the same two tools.

The chain proved in this module is
`ApproxHamDecompStatement → AbsorptionStatement → KOStatement → GKOStatementFixed →
Corollary 10.13`, whose first two implications are `koStatement_of_approx_and_absorption`
(`KOInputs.lean`), the third `gkoStatementFixed_of_KO` (`gkoStatementFixed_of_KO.lean`, the
paper's §10.2 argument) and the last `corollary_10_13_from_fixed`
(`corollary_10_13_odd_from_fixed.lean`).

## Cone hygiene

`gkoStatementFixed_of_KO` and its dependency closure currently `import Mathlib`, which imports
the root-level `Hypergraph` structure and makes the cone's
`ErdosFaberLovaszConjecture.Hypergraph` ambiguous.  Before this module can be imported by a
module of the cone (`Submission/EFL/...`) the import lines of the modules on the path must be
narrowed to the specific Mathlib modules they use (see the note in `HANDOFF.md` §3/§7: since
`Mathlib.Combinatorics.Hypergraph.Basic` is imported by nothing except `import Mathlib`, any set
of specific Mathlib imports is safe).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

noncomputable section

/-- **Theorem 10.8 (faithful form) from Kühn–Osthus' two tools.** -/
theorem gkoStatementFixed_of_approx_and_absorption (hApp : ApproxHamDecompStatement)
    (hAbs : AbsorptionStatement) : GKOStatementFixed :=
  gkoStatementFixed_of_KO (koStatement_of_approx_and_absorption hApp hAbs)

/-- **Corollary 10.13 (`cor:optcol`) from Kühn–Osthus' two tools.** -/
theorem corollary_10_13_of_approx_and_absorption (hApp : ApproxHamDecompStatement)
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
  corollary_10_13_from_fixed (gkoStatementFixed_of_approx_and_absorption hApp hAbs)

end

end Work.Deep.GKO
