import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K1
import Submission.Work.PTCert.Data.C2.RWAll
import Submission.Work.PTCert.Data.C2.L1
import Submission.Work.PTCert.Data.C2.A1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem ldldata_ok1 : ldlDataOK Cs1 Ws1 88 = true := by decide +kernel
theorem ldl_ok1_0 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [0,1,2,3,4,5] acc1_0 = some acc1_1 := by decide +kernel
theorem ldl_ok1_1 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [6,7,8,9] acc1_1 = some acc1_2 := by decide +kernel
theorem ldl_ok1_2 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [10,11,12,13] acc1_2 = some acc1_3 := by decide +kernel

end Submission.PTCert.C2K
end
