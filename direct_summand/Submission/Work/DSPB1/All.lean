import Submission.Work.DSPB1.Basic
import Submission.Work.DSPB1.Main
import Submission.Work.DSPB1.Varpi.varpi_isSMulRegular
import Submission.Work.DSPB1.Varpi.varpi_ne_zero
import Submission.Work.DSPB1.Varpi.varpi_not_isUnit
import Submission.Work.DSPB1.Varpi.p_mem_span_varpi
import Submission.Work.DSPB1.Varpi.isAdicComplete_span_varpi
import Submission.Work.DSPB1.Tilt.varpiTilt_ne_zero
import Submission.Work.DSPB1.Tilt.untilt_pow_mem_span
import Submission.Work.DSPB1.Tilt.varpiTiltShift_pow
import Submission.Work.DSPB1.Tilt.untilt_compatible_system

/-!
# DSPB1 — the whole area in one import

`import Submission.Work.DSPB1.All` gives the deliverable
`DSMap.Mix.perfectoid_varpiFlat_proved` (PB1, ϖ-flatness), the tilt API of
`Submission/Work/DSPB1/Basic.lean` (`Work.DSPB1.varpiTilt`, `varpiTilt_untilt`,
`varpiTiltShift`, `varpiTiltShift_untilt`, ...) and the delegated lemmas; see
`Submission/Work/DSPB1/NOTES.md` for the full interface list.

Scratch files (`Probe*.lean`, `Tilt/ProbeVT.lean`) are deliberately not imported here.
-/
