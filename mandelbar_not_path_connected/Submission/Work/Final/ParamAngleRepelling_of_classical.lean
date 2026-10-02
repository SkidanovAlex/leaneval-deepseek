import Mathlib
import Submission.Work.Final.Defs
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Land.Landing
import Submission.Work.Landing.Angle.exactPeriodAngle_paramAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Final

/-- **`ParamAngleRepelling` from the classical landing inputs of `Work.Landing`.**

The window angle `23/63` is a periodic angle of exact period `6`
(`Work.Landing.Angle.exactPeriodAngle_paramAngle`), so the classical landing input
`PeriodicRaysLand c` produces a point `z` at which the ray `R_c(23/63)` lands.  The even-period
landing dichotomy `EvenPeriodLandingDichotomy c` then says that `z` is either repelling or
lands on a parabolic cycle; the hypothesis `hpar` rules out the second alternative at `z` itself
(where the ray does land), so `z` is repelling. -/
theorem ParamAngleRepelling_of_classical {c : ℂ} (hper : Work.Landing.PeriodicRaysLand c)
    (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (hpar : ∀ (m : ℕ) (z : ℂ), Work.Landing.IsParabolic c m z →
      ¬ Work.Landing.landsAt c Work.Landing.paramAngle z) :
    Work.Final.ParamAngleRepelling c := by
  have hAngle : Work.Landing.IsPeriodicAngle Work.Landing.paramAngle :=
    ⟨6, by norm_num, Work.Landing.Angle.exactPeriodAngle_paramAngle.2.1⟩
  obtain ⟨z, hz⟩ := hper Work.Landing.paramAngle hAngle
  exact ParamAngleRepelling.of_landing hdich hz (fun m hm => hpar m z hm hz)

end Work.Final
