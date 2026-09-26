import Submission.Work.PTCert.Data.S0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem echunk_ok0 : eChunkOK cmT eM nT repT eC0 = true := by decide +kernel
theorem echunk_ok1 : eChunkOK cmT eM nT repT eC1 = true := by decide +kernel
theorem echunk_ok2 : eChunkOK cmT eM nT repT eC2 = true := by decide +kernel
theorem echunk_ok3 : eChunkOK cmT eM nT repT eC3 = true := by decide +kernel
theorem echunk_ok4 : eChunkOK cmT eM nT repT eC4 = true := by decide +kernel
theorem echunk_ok5 : eChunkOK cmT eM nT repT eC5 = true := by decide +kernel
theorem echunk_ok6 : eChunkOK cmT eM nT repT eC6 = true := by decide +kernel
theorem echunk_ok7 : eChunkOK cmT eM nT repT eC7 = true := by decide +kernel

end Submission.PTCert.C
end
