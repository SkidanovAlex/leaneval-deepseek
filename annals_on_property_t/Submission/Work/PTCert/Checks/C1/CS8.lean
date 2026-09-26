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

theorem cs_ok8 : classSumOK valT multT resT qC1 20 1208925819614629174706176 kl8 tl8 4000 = true := by decide +kernel

end Submission.PTCert.C1K
end
