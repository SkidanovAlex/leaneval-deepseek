import Submission.Work.PTCert.Data.S0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem repinv_ok : repInvOK cmT eM nT repT (List.range 611) = true := by decide +kernel
theorem reprow_ok : repRowOK cmT piT rowT repT repInfoT (List.range 611) = true := by decide +kernel
theorem repself_ok : repSelfOK eM repT (List.range 611) = true := by decide +kernel
theorem rowself_ok : rowSelfOK eM rowT repInfoT 18 = true := by decide +kernel
theorem rowidx_ok : rowIdxOK rowT rowIdxT 18 = true := by decide +kernel

end Submission.PTCert.C
end
