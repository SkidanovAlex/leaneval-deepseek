import Submission.Work.PTCert.Data.S0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem efaith_ok : eFaithfulOK eAll = true := by decide +kernel

end Submission.PTCert.C
end
