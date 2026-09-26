import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem tcl_ok2_0 : tclsOK canonT tclT (List.range' 2200 550) = true := by decide +kernel
theorem tcl_ok2_1 : tclsOK canonT tclT (List.range' 2750 550) = true := by decide +kernel

end Submission.PTCert.C
end
