import Submission.Work.PTCert.KernelExtra
import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.C2.Q

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem q_ok45 : qTabOK qT qC2 (List.range' 3645 81) = true := by decide +kernel
theorem q_ok46 : qTabOK qT qC2 (List.range' 3726 81) = true := by decide +kernel
theorem q_ok47 : qTabOK qT qC2 (List.range' 3807 81) = true := by decide +kernel
theorem q_ok48 : qTabOK qT qC2 (List.range' 3888 81) = true := by decide +kernel
theorem q_ok49 : qTabOK qT qC2 (List.range' 3969 81) = true := by decide +kernel
theorem q_ok50 : qTabOK qT qC2 (List.range' 4050 81) = true := by decide +kernel
theorem q_ok51 : qTabOK qT qC2 (List.range' 4131 81) = true := by decide +kernel
theorem q_ok52 : qTabOK qT qC2 (List.range' 4212 81) = true := by decide +kernel
theorem q_ok53 : qTabOK qT qC2 (List.range' 4293 81) = true := by decide +kernel

end Submission.PTCert.C2K
end
