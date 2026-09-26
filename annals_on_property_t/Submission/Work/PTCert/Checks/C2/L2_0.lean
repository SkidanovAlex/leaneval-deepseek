import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.K2
import Submission.Work.PTCert.Data.C2.RWAll
import Submission.Work.PTCert.Data.C2.L2
import Submission.Work.PTCert.Data.C2.A2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C2K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D2

theorem ldldata_ok2 : ldlDataOK Cs2 Ws2 59 = true := by decide +kernel
theorem ldl_ok2_0 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [0,1,2,3,4,5,6,7] acc2_0 = some acc2_1 := by decide +kernel
theorem ldl_ok2_1 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [8,9,10,11,12,13] acc2_1 = some acc2_2 := by decide +kernel
theorem ldl_ok2_2 : ldlSeg cmT eM repT repInfoT piIT piCodes rowTs 3 ks2 ys2 Cs2 Ws2 [14,15,16,17,18,19] acc2_2 = some acc2_3 := by decide +kernel

end Submission.PTCert.C2K
end
