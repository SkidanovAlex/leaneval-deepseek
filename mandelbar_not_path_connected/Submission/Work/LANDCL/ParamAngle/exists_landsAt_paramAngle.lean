import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.ParamAngle

/-- The window angle `paramAngle = 23/63` is a periodic angle under angle doubling
(exact period `6`, `Work.Landing.Angle.exactPeriodAngle_paramAngle`). -/
theorem isPeriodicAngle_paramAngle : Work.Landing.IsPeriodicAngle Work.Landing.paramAngle :=
  ⟨6, by norm_num, Work.Landing.Angle.exactPeriodAngle_paramAngle.2.1⟩

/-- From the classical landing input `PeriodicRaysLand c` (every periodic ray of `T_c` lands) the
parameter window ray `R_c(23/63)` lands: `23/63` is periodic. -/
theorem exists_landsAt_paramAngle {c : ℂ} (hper : Work.Landing.PeriodicRaysLand c) :
    ∃ z : ℂ, Work.Landing.landsAt c Work.Landing.paramAngle z :=
  hper Work.Landing.paramAngle isPeriodicAngle_paramAngle

end Work.LANDCL.ParamAngle
