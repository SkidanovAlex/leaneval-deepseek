import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem icl_ok3_0 : iclsOK canonT iclT (List.range' 4500 750) = true := by decide +kernel
theorem icl_ok3_1 : iclsOK canonT iclT (List.range' 5250 750) = true := by decide +kernel

end Submission.PTCert.C
end
