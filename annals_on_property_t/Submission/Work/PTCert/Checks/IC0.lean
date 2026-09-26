import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem canon_ok : canonOK canonT 7229 = true := by decide +kernel
theorem icl_ok0_0 : iclsOK canonT iclT (List.range' 0 750) = true := by decide +kernel
theorem icl_ok0_1 : iclsOK canonT iclT (List.range' 750 750) = true := by decide +kernel

end Submission.PTCert.C
end
