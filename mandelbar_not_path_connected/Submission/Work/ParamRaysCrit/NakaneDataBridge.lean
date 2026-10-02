/-
# From `NakaneInput` to the abstract parameter-plane data `Top.NakaneData Mb Phi`

The endgame (`Work.Top.not_isPathConnected_of_twoSidedPinch`, `Work.TopJordan.*`) and the
parameter-ray limit arguments (`Work.FSeed.ParamRayLimit`) are stated for an *abstract* datum

```lean
Work.Top.NakaneData Mb Φ
```

(a homeomorphism `Mbᶜ ≃ₜ {w | 1 < ‖w‖}` agreeing with `Φ`, `Φ = 0` on `Mb`, continuity of the
potential and its divergence at infinity).  This file supplies that datum at
`Mb = Work.ParamRays.Mb`, `Φ = Work.ParamRays.Phi` from the classical input bundle
`Work.ParamRays.NakaneInput`:

* the homeomorphism and its agreement with `Φ` are the field `homeo : NakaneHomeo`
  (Nakane's theorem, `Work.ParamRays.Phi_homeo`);
* `Φ` vanishes on the mandelbar (`Work.ParamRays.Phi_eq_zero_of_mem`);
* the potential is continuous (`Work.ParamRays.continuous_potential`) — note
  `Work.Top.potential Mb Phi` *is* `Work.ParamRays.potential` by `rfl`;
* the potential tends to `+∞` at infinity (`Work.ParamRaysCrit.NakaneData.potential_tendsto_atTop`,
  from the uniform asymptotic `Φ c / c → 1` together with `Mb ⊆ closedBall 0 2`).

Consequently `Work.Top.NakaneData Mb Phi` is **not vacuous**: it follows from the (now true)
classical inputs — in particular from the *repaired* `BottcherExists`, which is a statement about
critical Böttcher coordinates and is no longer false off the mandelbar.

## Main result

* `Work.ParamRaysCrit.nakaneData : NakaneInput → Top.NakaneData Mb Phi`.
* `Work.ParamRaysCrit.nonempty_nakaneData : NakaneInput → Nonempty (Top.NakaneData Mb Phi)`.
-/
import Submission.Work.ParamRays.continuous_potential
import Submission.Work.ParamRaysCrit.NakaneData.potential_tendsto_atTop
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology

namespace Work.ParamRaysCrit

/-- **The parameter-plane Nakane data from the classical inputs.**  Every `NakaneInput` yields
`Work.Top.NakaneData Work.ParamRays.Mb Work.ParamRays.Phi`. -/
noncomputable def nakaneData (h : Work.ParamRays.NakaneInput) :
    Work.Top.NakaneData Work.ParamRays.Mb Work.ParamRays.Phi where
  e := h.homeo.choose
  he := fun c => (h.homeo.choose_spec c).symm
  Phi_eq_zero_of_mem := fun c hc => Work.ParamRays.Phi_eq_zero_of_mem hc
  continuous_potential := Work.ParamRays.continuous_potential h
  tendsto_potential := Work.ParamRaysCrit.NakaneData.potential_tendsto_atTop h

/-- The same, as a `Nonempty` statement. -/
theorem nonempty_nakaneData (h : Work.ParamRays.NakaneInput) :
    Nonempty (Work.Top.NakaneData Work.ParamRays.Mb Work.ParamRays.Phi) :=
  ⟨nakaneData h⟩

end Work.ParamRaysCrit
