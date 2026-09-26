import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem kl_perm : isPermOf (List.flatten (kl0 ++ kl1 ++ kl2 ++ kl3 ++ kl4 ++ kl5 ++ kl6 ++ kl7 ++ kl8 ++ kl9 ++ kl10 ++ kl11 ++ kl12 ++ kl13 ++ kl14)) (allKeys ngL) = true := by decide +kernel
theorem tl_perm : isPermOf (List.flatten (tl0 ++ tl1 ++ tl2 ++ tl3 ++ tl4 ++ tl5 ++ tl6 ++ tl7 ++ tl8 ++ tl9 ++ tl10 ++ tl11 ++ tl12 ++ tl13 ++ tl14)) (List.range 6561) = true := by decide +kernel

end Submission.PTCert.C
end
