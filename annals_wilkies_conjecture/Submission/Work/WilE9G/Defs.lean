/-
  Subproject WilE9G (curric-46): the *geometric input* of area E9 (BNZ §3), in its
  almost-everywhere form.

  `Work.WilE9.Sharp.EffStrat` is FALSE (see `Work.WilE9.Sharp.not_effStrat_unrestricted`
  and the design `sources/wilkiesE3E9/wilkies_E3E9_gaps.md` §GAP 2): an isolated-point
  component forces a `Good` stratum inside `{z₀}`, which the fibre Jacobian condition
  contradicts.  The corrected input `EffStratAE` below

  * leaves the number `m'` of hidden (fibre) coordinates of a stratum FREE — a stratum
    carries Lagrange multipliers for the maximisation over the fibre;
  * attaches to each stratum a point `q` and only ever uses
    `connectedComponentIn E.X.set q`, and requires that component to *project into* the
    `*`-piece `P = stratProj '' connectedComponentIn X.set z₀`;
  * replaces the density conclusion by an almost-everywhere covering: there is a null set
    `N ⊆ ℝⁿ` such that every `y ∈ P` with `Fin.init y ∉ N` and a FINITE `P`-fibre over
    `Fin.init y` lies in the projection of some stratum component.

  This is the statement `Work.WilE9G.EffStratAE_of_frozen` derives from the two frozen
  hypotheses `E2_components` and `E5_strat` (the ambient instance `p = 0`).

  **The definition below is copied VERBATIM from the design file
  `sources/wilkiesE3E9/wilkies_E3E9_gaps.lean` (the `def EffStratAE`, namespace
  `WilkiesDesign.E.Gaps`).  It must not be changed: area WilE9 imports this module for its
  hypothesis.**
-/
import Submission.Work.WilE9.Sharp.EffInput
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-- **The corrected geometric input of E9** (this replaces `EffStrat`).  Strata come with a point
`q`; only the component of `E.X.set` through `q` is used, and that component projects into the
`*`-piece `P = stratProj '' connectedComponentIn X.set z₀`.  Covering is exact, but only over base
points outside a null set `N` at which `P` has a finite fibre.  This is all E9 needs: over the open
cube, `Z` is the ψ-graph of `f` plus at most two boundary points per fibre.  The number of hidden
coordinates `m'` of a stratum is free (it carries Lagrange multipliers). -/
def EffStratAE : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (n m : ℕ) (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ),
      X.fmt ≤ F → z₀ ∈ X.set →
      ∃ L : List (Σ m' : ℕ, EffStratum n m' × (Fin (n + (1 + m')) → ℝ)),
        L.length ≤ b.eval X.deg ∧
        (∀ E ∈ L, E.2.1.X.fmt ≤ a ∧ E.2.1.deg ≤ b.eval X.deg ∧
          E.2.1.X.basics.length ≤ b.eval X.deg ∧ E.2.1.Good ∧ E.2.2 ∈ E.2.1.X.set ∧
          ∀ w ∈ connectedComponentIn E.2.1.X.set E.2.2,
            stratProj w ∈ stratProj '' connectedComponentIn X.set z₀) ∧
        ∃ N : Set (Fin n → ℝ), MeasureTheory.volume N = 0 ∧
          ∀ y ∈ stratProj '' connectedComponentIn X.set z₀, Fin.init y ∉ N →
            {y' | y' ∈ stratProj '' connectedComponentIn X.set z₀ ∧
              Fin.init y' = Fin.init y}.Finite →
            y ∈ ⋃ E ∈ L, stratProj '' connectedComponentIn E.2.1.X.set E.2.2

end Work.WilE9G
