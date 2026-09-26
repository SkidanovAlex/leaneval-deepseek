import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K0
import Submission.Work.PTCert.Data.C2.RWAll
import Submission.Work.PTCert.Data.C2.L0
import Submission.Work.PTCert.Data.C2.A0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem ldl_ok0_103 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [110] acc0_103 = some acc0_104 := by decide +kernel
theorem ldl_ok0_104 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [111] acc0_104 = some acc0_105 := by decide +kernel
theorem ldl_ok0_105 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [112] acc0_105 = some acc0_106 := by decide +kernel
theorem ldl_ok0_106 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 0 ks0 ys0 Cs0 Ws0 [113] acc0_106 = some acc0_107 := by decide +kernel

end Submission.PTCert.C2K
end
