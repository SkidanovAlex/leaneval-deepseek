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

theorem ldl_ok0_39 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [46] acc0_39 = some acc0_40 := by decide +kernel
theorem ldl_ok0_40 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [47] acc0_40 = some acc0_41 := by decide +kernel
theorem ldl_ok0_41 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [48] acc0_41 = some acc0_42 := by decide +kernel
theorem ldl_ok0_42 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [49] acc0_42 = some acc0_43 := by decide +kernel

end Submission.PTCert.C1K
end
