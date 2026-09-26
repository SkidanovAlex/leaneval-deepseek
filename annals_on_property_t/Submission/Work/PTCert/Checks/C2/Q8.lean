import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok72 : qTabOK qT qC2 (List.range' 5832 81) = true := by decide +kernel
theorem q_ok73 : qTabOK qT qC2 (List.range' 5913 81) = true := by decide +kernel
theorem q_ok74 : qTabOK qT qC2 (List.range' 5994 81) = true := by decide +kernel
theorem q_ok75 : qTabOK qT qC2 (List.range' 6075 81) = true := by decide +kernel
theorem q_ok76 : qTabOK qT qC2 (List.range' 6156 81) = true := by decide +kernel
theorem q_ok77 : qTabOK qT qC2 (List.range' 6237 81) = true := by decide +kernel
theorem q_ok78 : qTabOK qT qC2 (List.range' 6318 81) = true := by decide +kernel
theorem q_ok79 : qTabOK qT qC2 (List.range' 6399 81) = true := by decide +kernel
theorem q_ok80 : qTabOK qT qC2 (List.range' 6480 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
