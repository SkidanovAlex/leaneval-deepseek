import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K1
import Submission.Work.PTCert.Data.C1.RWAll
import Submission.Work.PTCert.Data.C1.L1
import Submission.Work.PTCert.Data.C1.A1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ldl_ok1_19 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [62,63,64,65] acc1_19 = some acc1_20 := by decide +kernel
theorem ldl_ok1_20 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [66,67,68,69] acc1_20 = some acc1_21 := by decide +kernel
theorem ldl_ok1_21 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [70,71,72,73,74] acc1_21 = some acc1_22 := by decide +kernel
theorem ldl_ok1_22 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 1 ks1 ys1 Cs1 Ws1 [75,76,77,78,79,80,81,82,83] acc1_22 = some acc1_23 := by decide +kernel

end Submission.PTCert.C1K
end
