import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaFromEpsLeafA/StripDefs` — the two angular truncations `stripLo`/`stripHi`

The two truncations used by sub-leaves **(A)** (`sinpow_mixed_Jeps_le_strip`) and **(B)**
(`tendsto_EpsSq_strip`) of the θ-uniformity chapter, with the **same qualified names**
(`Work.FTS.EpsEngine.ThetaFromEps.stripLo`, `Work.FTS.EpsEngine.ThetaFromEps.stripHi`) and the
same bodies as the original declarations inside `EpsEngine/ThetaFromEps.lean`.

## Why this module exists

`EpsEngine/ThetaFromEps.lean` currently *imports* the two sub-leaf modules
(`ThetaFromEpsLeafB.tendsto_EpsSq_strip`, and it is meant to import
`ThetaFromEpsLeafA.sinpow_mixed_Jeps_le_strip` as well), while those leaf modules need the
truncations — which until now were declared only inside `ThetaFromEps.lean`.  That is an import
cycle, and Lake refuses to build any module of the cone.

Declaring the truncations here breaks the cycle in the only consistent way: the leaf modules (and
everything else) get the definitions from this module, and `EpsEngine/ThetaFromEps.lean` must
**drop its own `stripLo`/`stripHi` declarations and import this module instead** (otherwise the
same name would be declared twice in one environment).  The definitions are byte-for-byte the
originals, so nothing changes mathematically.

This is the same workaround as the `Aux/` twin modules of `Work.FTS.EllipticEst` documented in
`HANDOFF.md` ("keep a buildable twin with the same namespace and declaration name, which is the
copy consumers import").
-/

noncomputable section

namespace Work.FTS.EpsEngine.ThetaFromEps

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-- truncation of `g` to the angular strip `θ ≤ φ`. -/
def stripLo (φ : ℝ) (g : Fn) : Fn := fun z θ => if θ ≤ φ then g z θ else 0

/-- truncation of `g` to the angular strip `θ ≥ π/2 - φ`. -/
def stripHi (φ : ℝ) (g : Fn) : Fn := fun z θ => if Real.pi / 2 - φ ≤ θ then g z θ else 0

end Work.FTS.EpsEngine.ThetaFromEps
