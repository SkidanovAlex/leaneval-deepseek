import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok27 : qTabOK qT qC2 (List.range' 2187 81) = true := by decide +kernel
theorem q_ok28 : qTabOK qT qC2 (List.range' 2268 81) = true := by decide +kernel
theorem q_ok29 : qTabOK qT qC2 (List.range' 2349 81) = true := by decide +kernel
theorem q_ok30 : qTabOK qT qC2 (List.range' 2430 81) = true := by decide +kernel
theorem q_ok31 : qTabOK qT qC2 (List.range' 2511 81) = true := by decide +kernel
theorem q_ok32 : qTabOK qT qC2 (List.range' 2592 81) = true := by decide +kernel
theorem q_ok33 : qTabOK qT qC2 (List.range' 2673 81) = true := by decide +kernel
theorem q_ok34 : qTabOK qT qC2 (List.range' 2754 81) = true := by decide +kernel
theorem q_ok35 : qTabOK qT qC2 (List.range' 2835 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
