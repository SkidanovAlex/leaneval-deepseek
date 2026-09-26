import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K2
import Submission.Work.PTCert.Data.C1.RWAll
import Submission.Work.PTCert.Data.C1.L2
import Submission.Work.PTCert.Data.C1.A2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem ldl_ok2_3 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [20,21,22,23,24] acc2_3 = some acc2_4 := by decide +kernel
theorem ldl_ok2_4 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [25,26,27,28,29,30] acc2_4 = some acc2_5 := by decide +kernel
theorem ldl_ok2_5 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [31,32,33,34,35,36] acc2_5 = some acc2_6 := by decide +kernel
theorem ldl_ok2_6 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [37,38,39,40,41,42,43] acc2_6 = some acc2_7 := by decide +kernel

end Submission.PTCert.C1K
end
