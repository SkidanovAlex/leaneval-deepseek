import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok0 : qTabOK qT qC2 (List.range' 0 81) = true := by decide +kernel
theorem q_ok1 : qTabOK qT qC2 (List.range' 81 81) = true := by decide +kernel
theorem q_ok2 : qTabOK qT qC2 (List.range' 162 81) = true := by decide +kernel
theorem q_ok3 : qTabOK qT qC2 (List.range' 243 81) = true := by decide +kernel
theorem q_ok4 : qTabOK qT qC2 (List.range' 324 81) = true := by decide +kernel
theorem q_ok5 : qTabOK qT qC2 (List.range' 405 81) = true := by decide +kernel
theorem q_ok6 : qTabOK qT qC2 (List.range' 486 81) = true := by decide +kernel
theorem q_ok7 : qTabOK qT qC2 (List.range' 567 81) = true := by decide +kernel
theorem q_ok8 : qTabOK qT qC2 (List.range' 648 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
