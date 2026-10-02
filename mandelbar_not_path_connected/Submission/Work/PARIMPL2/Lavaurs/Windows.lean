/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.Windows` — the chart-radius hypothesis of the L2 model estimates

Design: `Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.4.  The two geometric windows
`Work.PARIMPL2.WinG` / `WoutG` of `Lavaurs.Defs` live in the `c₀`-chart `w₀ = -P.s c₀/(z - d.z₁)`;
to read the local model of the *parameter* `c` on them one needs first that they sit inside the
chart ball `‖ζ_c‖ < P.r` of the normal form at `c`, uniformly for `c` near `c₀`.  That is the
property `RchOK` below, and `exists_Rch` (delegated) proves it for all `R` above a threshold.
-/
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open Work.PARIMPL (ParNormal chartZeta)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The chart-radius condition**: for every imaginary bound `H` with `R ≥ 8 (H+1)`, the two
windows of radius `R` sit inside the chart ball `‖ζ_c‖ < P.r/2` for all `c ∈ P.Nm` close enough to
`c₀` (the radius `ρ` of the parameter ball may depend on `R`). -/
def RchOK (P : ParNormal d) (R : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ H : ℝ, R ≥ 8 * (H + 1) →
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z ∈ WinG P R H ∪ WoutG P R H, ‖chartZeta P c z‖ < P.r / 2


/-- **The chart-radius condition, together with the two size conditions that the model transit
needs.**

* `16 ≤ R * P.r` lets `Work.PARIMPL2.Lavaurs.transit_model` know that the model orbit (which stays
  within `8/R` of the chart origin) stays strictly inside the germ ball `‖ζ‖ < P.r`;
* `64 * (P.A + ‖P.h1 c₀‖ + 2) ≤ R` makes the germ as close to `τ` as the transit regime requires
  (`‖h ζ - τ‖ ≤ A‖ζ‖² + ‖h1‖‖ζ‖` is `≤ 1/8` on the orbit); the constant `‖P.h1 c₀‖ + 1` is a local
  bound for `‖P.h1 c‖` near `c₀` (`P.cont_h1`);
* `(‖P.h1 c₀‖ + 2)(1 + log R) ≤ 3R/4` is the *reachability* condition of the transit: the level
  `Re Ũ = R` is met by the model orbit only if `‖κ‖ log R ≲ R`
  (`NOTES_FALSE_transit_model_third.md`).

All three are harmless because `R` is chosen freely large in the assembly.  `exists_Rch'` produces
`RchOK'` from `exists_Rch`. -/
def RchOK' (P : ParNormal d) (R : ℝ) : Prop :=
  RchOK P R ∧ 16 ≤ R * P.r ∧ 64 * (P.A + ‖P.h1 c₀‖ + 2) ≤ R ∧
    (‖P.h1 c₀‖ + 2) * (1 + Real.log R) ≤ 3 * R / 4

end Work.PARIMPL2

end
