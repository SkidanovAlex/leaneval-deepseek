import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls
import Submission.Work.PTCert.Data.R0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem gcl_ok0_0 : gclsOK canonT gclT grepT0 0 0 0 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] = true := by decide +kernel

end Submission.PTCert.C
end
