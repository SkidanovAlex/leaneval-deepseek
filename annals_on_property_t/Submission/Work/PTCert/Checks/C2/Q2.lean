import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok18 : qTabOK qT qC2 (List.range' 1458 81) = true := by decide +kernel
theorem q_ok19 : qTabOK qT qC2 (List.range' 1539 81) = true := by decide +kernel
theorem q_ok20 : qTabOK qT qC2 (List.range' 1620 81) = true := by decide +kernel
theorem q_ok21 : qTabOK qT qC2 (List.range' 1701 81) = true := by decide +kernel
theorem q_ok22 : qTabOK qT qC2 (List.range' 1782 81) = true := by decide +kernel
theorem q_ok23 : qTabOK qT qC2 (List.range' 1863 81) = true := by decide +kernel
theorem q_ok24 : qTabOK qT qC2 (List.range' 1944 81) = true := by decide +kernel
theorem q_ok25 : qTabOK qT qC2 (List.range' 2025 81) = true := by decide +kernel
theorem q_ok26 : qTabOK qT qC2 (List.range' 2106 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
