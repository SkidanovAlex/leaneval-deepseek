import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem tcl_ok5_0 : tclsOK canonT tclT (List.range' 5500 550) = true := by decide +kernel
theorem tcl_ok5_1 : tclsOK canonT tclT (List.range' 6050 511) = true := by decide +kernel

end Submission.PTCert.C
end
