import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok36 : qTabOK qT qC2 (List.range' 2916 81) = true := by decide +kernel
theorem q_ok37 : qTabOK qT qC2 (List.range' 2997 81) = true := by decide +kernel
theorem q_ok38 : qTabOK qT qC2 (List.range' 3078 81) = true := by decide +kernel
theorem q_ok39 : qTabOK qT qC2 (List.range' 3159 81) = true := by decide +kernel
theorem q_ok40 : qTabOK qT qC2 (List.range' 3240 81) = true := by decide +kernel
theorem q_ok41 : qTabOK qT qC2 (List.range' 3321 81) = true := by decide +kernel
theorem q_ok42 : qTabOK qT qC2 (List.range' 3402 81) = true := by decide +kernel
theorem q_ok43 : qTabOK qT qC2 (List.range' 3483 81) = true := by decide +kernel
theorem q_ok44 : qTabOK qT qC2 (List.range' 3564 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
