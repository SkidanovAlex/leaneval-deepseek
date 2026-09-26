import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok9 : qTabOK qT qC2 (List.range' 729 81) = true := by decide +kernel
theorem q_ok10 : qTabOK qT qC2 (List.range' 810 81) = true := by decide +kernel
theorem q_ok11 : qTabOK qT qC2 (List.range' 891 81) = true := by decide +kernel
theorem q_ok12 : qTabOK qT qC2 (List.range' 972 81) = true := by decide +kernel
theorem q_ok13 : qTabOK qT qC2 (List.range' 1053 81) = true := by decide +kernel
theorem q_ok14 : qTabOK qT qC2 (List.range' 1134 81) = true := by decide +kernel
theorem q_ok15 : qTabOK qT qC2 (List.range' 1215 81) = true := by decide +kernel
theorem q_ok16 : qTabOK qT qC2 (List.range' 1296 81) = true := by decide +kernel
theorem q_ok17 : qTabOK qT qC2 (List.range' 1377 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
