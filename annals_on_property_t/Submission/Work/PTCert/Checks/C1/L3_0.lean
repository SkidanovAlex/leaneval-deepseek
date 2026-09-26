import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K3
import Submission.Work.PTCert.Data.C1.RWAll
import Submission.Work.PTCert.Data.C1.L3
import Submission.Work.PTCert.Data.C1.A3

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ldldata_ok3 : ldlDataOK Cs3 Ws3 27 = true := by decide +kernel
theorem ldl_ok3_0 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 7 ks3 ys3 Cs3 Ws3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] acc3_0 = some acc3_1 := by decide +kernel
theorem ldl_ok3_1 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 7 ks3 ys3 Cs3 Ws3 [23,24,25,26] acc3_1 = some acc3_2 := by decide +kernel

end Submission.PTCert.C1K
end
