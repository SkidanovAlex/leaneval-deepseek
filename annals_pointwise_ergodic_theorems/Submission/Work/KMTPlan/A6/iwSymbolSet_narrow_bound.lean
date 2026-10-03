/-
# Narrowness of the IW symbol over a non-aliasing frequency set

Let `A = diffFreqs ρ l ⊆ ℝ/ℤ` be the exact-height frequency set of the Ionescu–Wainger
multiplier `Tm ρ l φ`, and let `Φ : ℝ/ℤ → ℂ` be a symbol of sup norm `≤ C` which is *supported in
the arc* `ℝ_{≤K}`.  If the frequencies are *non-aliasing* at scale `K` — i.e. the arcs
`α + ℝ_{≤K}`, `α ∈ A`, are pairwise disjoint in `ℝ/ℤ` — then at every frequency `ξ` at most one of
the terms `Φ (ξ - α)`, `α ∈ A`, of the IW symbol

`iwSymbolSet A Φ ξ = ∑_{α ∈ A} Φ (ξ - α)`

can be nonzero (a nonzero term `Φ (ξ - α)` forces `ξ ∈ α + ℝ_{≤K}`).  Consequently the symbol is
bounded pointwise by `C`:

`∀ ξ, ‖iwSymbolSet (diffFreqs ρ l) Φ ξ‖ ≤ C`.

This is the "narrow" pointwise bound for the §5 IW pieces: on the model tuple the symbol
`Φ = varphiNt N k t` is supported in the narrow arc `|ξ| ≤ 2^{⌊-Cρ 2^{ρl}⌋}` whose height `K` is
exactly the scale at which the arithmetic frequencies `diffFreqs ρ l` are non-aliasing, so the sum
over the frequencies degenerates to at most one term.

The mathematics is a one-line consequence of the general statement
`Work.Analysis.IonescuWainger.norm_iwSymbolSet_le_of_nonAliasing` (proved in
`Submission/Work/Analysis/IonescuWainger/norm_iwOpSet_le.lean`), which performs exactly this
diagonal collapse for an arbitrary non-aliasing frequency set `A` and arbitrary `SupportedInArc`
symbol `Φ`; we simply instantiate it at `A = diffFreqs ρ l`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BandDecomp

namespace Work.KMTPlan.A6

theorem iwSymbolSet_narrow_bound (ρ : ℝ) (l : ℕ) (K : ℤ)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hΦb : ∀ ξ : Work.Analysis.IonescuWainger.Circle, ‖Φ ξ‖ ≤ C)
    (hΦs : Work.Analysis.IonescuWainger.SupportedInArc K Φ)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing K (Work.KMTAreas.A7.diffFreqs ρ l)) :
    ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) Φ ξ‖ ≤ C :=
  Work.Analysis.IonescuWainger.norm_iwSymbolSet_le_of_nonAliasing hNA hΦs hC hΦb

end Work.KMTPlan.A6
