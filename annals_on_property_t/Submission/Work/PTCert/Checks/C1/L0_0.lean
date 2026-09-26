import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K0
import Submission.Work.PTCert.Data.C1.RWAll
import Submission.Work.PTCert.Data.C1.L0
import Submission.Work.PTCert.Data.C1.A0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ldldata_ok0 : ldlDataOK Cs0 Ws0 161 = true := by decide +kernel
theorem ldl_ok0_0 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [0,1,2] acc0_0 = some acc0_1 := by decide +kernel
theorem ldl_ok0_1 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [3,4] acc0_1 = some acc0_2 := by decide +kernel
theorem ldl_ok0_2 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [5,6] acc0_2 = some acc0_3 := by decide +kernel

end Submission.PTCert.C1K
end
