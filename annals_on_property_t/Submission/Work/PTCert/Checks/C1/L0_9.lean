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

theorem ldl_ok0_35 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [42] acc0_35 = some acc0_36 := by decide +kernel
theorem ldl_ok0_36 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [43] acc0_36 = some acc0_37 := by decide +kernel
theorem ldl_ok0_37 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [44] acc0_37 = some acc0_38 := by decide +kernel
theorem ldl_ok0_38 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [45] acc0_38 = some acc0_39 := by decide +kernel

end Submission.PTCert.C1K
end
