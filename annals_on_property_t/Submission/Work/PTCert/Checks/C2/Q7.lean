import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok63 : qTabOK qT qC2 (List.range' 5103 81) = true := by decide +kernel
theorem q_ok64 : qTabOK qT qC2 (List.range' 5184 81) = true := by decide +kernel
theorem q_ok65 : qTabOK qT qC2 (List.range' 5265 81) = true := by decide +kernel
theorem q_ok66 : qTabOK qT qC2 (List.range' 5346 81) = true := by decide +kernel
theorem q_ok67 : qTabOK qT qC2 (List.range' 5427 81) = true := by decide +kernel
theorem q_ok68 : qTabOK qT qC2 (List.range' 5508 81) = true := by decide +kernel
theorem q_ok69 : qTabOK qT qC2 (List.range' 5589 81) = true := by decide +kernel
theorem q_ok70 : qTabOK qT qC2 (List.range' 5670 81) = true := by decide +kernel
theorem q_ok71 : qTabOK qT qC2 (List.range' 5751 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
