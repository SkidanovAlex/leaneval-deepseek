/-
# The dynamical `NakaneData` for the filled Julia set (the `EL` bridge interface)

The `EL` bridge in the dynamical plane consumes `Work.Top.NakaneData (filledJulia c) (dynPhi c)`.
This file assembles that structure from the pieces exported by `DynBottcher.lean` (the homeomorphism
field `e`, its agreement `he`, and `dynPhi` vanishing on the filled Julia set) and
`dynNakane_potential.lean` (continuity of the potential and the potential tending to infinity).

```lean
noncomputable def dynNakane (h : DynBottcherHomeo c) :
    Work.Top.NakaneData (filledJulia c) (dynPhi c)
```

`DynBottcherHomeo c` is the dynamical Böttcher input (Böttcher's theorem: the Böttcher coordinate
is a homeomorphism of the escaping set onto the exterior of the unit disc).  It is *not* supplied by
`Work.Bottcher.bottcher`, whose product formula fails the Böttcher equation
(`Work.Bottcher.Core.bottcher_comm_Tantibar_false`); the object `dynPhi c` is the canonical
Böttcher coordinate selected by `IsDynBottcher` and `isDynBottcher_unique` instead, which is what
`Work.Landing.landsAt` quantifies over.
-/
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.ParamRays.dynNakane_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate
open Classical

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The dynamical Nakane interface.**  The dynamical Böttcher coordinate `dynPhi c` realises the
abstract `Work.Top.NakaneData` for `Mb := filledJulia c`, given the dynamical Böttcher
homeomorphism input.

**Scope.**  This interface is only instantiated at parameters `c ∈ M*` (the `EL` bridge and
`FSeed`): `DynBottcherHomeo c` implies `DynBottcherExists c`, which is false for `c ∉ M*`. -/
noncomputable def dynNakane {c : ℂ} (h : DynBottcherHomeo c) :
    Work.Top.NakaneData (filledJulia c) (dynPhi c) where
  e := h.2.choose
  he := fun z => h.2.choose_spec z
  Phi_eq_zero_of_mem := fun z hz => dynPhi_eq_zero_of_mem hz
  continuous_potential := (dynNakane_potential h).1
  tendsto_potential := (dynNakane_potential h).2

end Work.ParamRays
