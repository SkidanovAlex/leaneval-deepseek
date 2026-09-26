import Mathlib
import Submission.Work.Drive.Mono.AE
import Submission.Work.Drive.Mono.Constancy
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Final.sweep_mono

/-!
# The bridges from the fleet's residuals to the a.e. crux

`Work.Drive.Mono.CruxCoreWdAE` (the residual of
`Submission/Work/Drive/Mono/pardon_unconditional_mono.lean`) is *implied* by every form of the
residual the fleet has been pursuing, so a proof of any of them finishes the deliverable:

* `cruxCoreWdAE_of_tiltedSweepMono` — from `Work.Drive.Final.TiltedSweepMono`;
* `cruxCoreWdAE_of_sweepSpanConst` — from `Work.Drive.Mono.SweepSpanConst`;
* `cruxCoreWdAE_of_traceDataWExists` — from `Work.Drive.Mono.TiltedTraceDataWExists`.

This module is kept apart from `pardon_unconditional_mono.lean` so that the deliverable itself
depends only on `Mono/AE.lean` (and hence does not break while the trace-data residual is being
edited).
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

namespace Work.Drive.Mono

/-- **The tilted sweep `TiltedSweepMono` gives the a.e. crux** (through the ordinary crux). -/
theorem cruxCoreWdAE_of_tiltedSweepMono (h : Work.Drive.Final.TiltedSweepMono) :
    ∀ p q : ℕ, CruxCoreWdAE p q :=
  cruxCoreWdAE_of_cruxCoreWd (Work.Drive.Final.cruxCoreWd_of_tiltedSweepMono h)

/-- **The constancy form of the residual gives the a.e. crux.** -/
theorem cruxCoreWdAE_of_sweepSpanConst (h : SweepSpanConst) : ∀ p q : ℕ, CruxCoreWdAE p q :=
  cruxCoreWdAE_of_tiltedSweepMono (tiltedSweepMono_of_sweepSpanConst h)

/-- **The trace-data residual gives the a.e. crux.** -/
theorem cruxCoreWdAE_of_traceDataWExists (h : TiltedTraceDataWExists) :
    ∀ p q : ℕ, CruxCoreWdAE p q :=
  cruxCoreWdAE_of_sweepSpanConst (sweepSpanConst_of_tiltedTraceDataWExists h)

end Work.Drive.Mono
