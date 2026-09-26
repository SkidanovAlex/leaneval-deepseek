import Mathlib
import ChallengeDeps

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# `C^∞` knots (as opposed to the analytic knots of `IsSmoothKnot`)

In this Mathlib `ContDiff 𝕜 ⊤` is **analyticity** (`⊤ = ω`), so `ChallengeDeps.IsSmoothKnot` — the
notion appearing in `IsUnknotted` — is a *real-analytic* knot.  Every construction that produces a
family of knots by *smooth* operations (mollification, convolution with a smooth kernel, smoothing a
piecewise-defined family) produces `C^∞` slices and typically *not* analytic ones; those slices must
therefore be smoothed separately (`Work.Drive.exists_analytic_periodic_close`,
`Work.Drive.exists_analytic_close_twoVar`).

`IsCInfKnot` is the `C^∞` analogue of `IsSmoothKnot`, written with the workspace convention
`((⊤ : ℕ∞) : WithTop ℕ∞)` for `C^∞` (see `HANDOFF.md`): same four clauses (regularity, periodicity,
injectivity on one period, nonvanishing velocity), with `C^∞` in place of analyticity.
-/

namespace Work.Drive

/-- A **`C^∞` knot**: a `C^∞`, `period`-periodic, regular simple closed curve.  (`IsSmoothKnot`
asks for an *analytic* curve; `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r` is `C^∞`.) -/
def IsCInfKnot (r : ℝ → Space) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ Function.Periodic r period ∧
    Set.InjOn r (Set.Ico (0 : ℝ) period) ∧ ∀ t : ℝ, velocity r t ≠ 0

/-- Analytic knots are `C^∞` knots. -/
theorem IsSmoothKnot.toCInf {r : ℝ → Space} (h : IsSmoothKnot r) : IsCInfKnot r :=
  ⟨h.smooth.of_le le_top, h.periodic, h.injective_on_period, h.regular⟩

/-- Analytic knots are `C^∞` knots, as a `Prop`-rewriting form. -/
theorem isCInfKnot_of_isSmoothKnot {r : ℝ → Space} (h : IsSmoothKnot r) : IsCInfKnot r :=
  IsSmoothKnot.toCInf h

end Work.Drive
