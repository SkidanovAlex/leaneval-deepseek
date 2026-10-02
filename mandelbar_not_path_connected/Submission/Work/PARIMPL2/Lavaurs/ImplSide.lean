/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.ImplSide` — the implosion-side export

The *second* half of the delivered `Work.PARIMPL.ParImplInputs`, in the form the final wiring of
`Submission/Work/Final/` consumes (`Work.PARIMPL.Bridge.implSide_toFinal`): the implosion side
`P.Nm` of the parameter normal form is open, accumulates at `c₀` (FBif) and has lost the period-`5`
point (`periodFiveGone`, from the splitting `swap`).

Both inputs are *delivered and sorry-free* (`Work.PARIMPL.Nm_mem_closure`,
`Work.PARIMPL.periodFiveGone`), so this file is unconditional: nothing of this area's analytic
chain (`LavaursPhase`, N1, N2) is needed for the `impl` half. -/
import Submission.Work.PARIMPL.Main
import Submission.Work.PARIMPL.Nm_mem_closure

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

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The implosion side** `ImplSide c₀ d.z₁ P.Nm` from the parameter normal form alone
(`P.toImplSide` with FBif's `Nm_mem_closure` and the delivered `periodFiveGone`). -/
theorem implSide (P : ParNormal d) : Work.PARIMPL.ImplSide c₀ d.z₁ P.Nm :=
  P.toImplSide (Work.PARIMPL.Nm_mem_closure d P) (Work.PARIMPL.periodFiveGone d P)

end Work.PARIMPL2.Lavaurs

end
