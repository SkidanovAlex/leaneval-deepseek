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

theorem ldl_ok1_7 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [26,27,28] acc1_7 = some acc1_8 := by decide +kernel
theorem ldl_ok1_8 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [29,30,31] acc1_8 = some acc1_9 := by decide +kernel
theorem ldl_ok1_9 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [32,33,34] acc1_9 = some acc1_10 := by decide +kernel
theorem ldl_ok1_10 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [35,36,37] acc1_10 = some acc1_11 := by decide +kernel

end Submission.PTCert.C2K
end
