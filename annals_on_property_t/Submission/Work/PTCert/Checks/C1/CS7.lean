import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls
import Submission.Work.PTCert.Data.C1.V
import Submission.Work.PTCert.Data.C1.Res

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C1K
open Submission.PTCert Submission.PTCert.D Submission.PTCert.D1

theorem cs_ok7 : classSumOK valT multT resT qC1 20 1208925819614629174706176 kl7 tl7 3500 = true := by decide +kernel

end Submission.PTCert.C1K
end
