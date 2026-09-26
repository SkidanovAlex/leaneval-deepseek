import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok54 : qTabOK qT qC2 (List.range' 4374 81) = true := by decide +kernel
theorem q_ok55 : qTabOK qT qC2 (List.range' 4455 81) = true := by decide +kernel
theorem q_ok56 : qTabOK qT qC2 (List.range' 4536 81) = true := by decide +kernel
theorem q_ok57 : qTabOK qT qC2 (List.range' 4617 81) = true := by decide +kernel
theorem q_ok58 : qTabOK qT qC2 (List.range' 4698 81) = true := by decide +kernel
theorem q_ok59 : qTabOK qT qC2 (List.range' 4779 81) = true := by decide +kernel
theorem q_ok60 : qTabOK qT qC2 (List.range' 4860 81) = true := by decide +kernel
theorem q_ok61 : qTabOK qT qC2 (List.range' 4941 81) = true := by decide +kernel
theorem q_ok62 : qTabOK qT qC2 (List.range' 5022 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
