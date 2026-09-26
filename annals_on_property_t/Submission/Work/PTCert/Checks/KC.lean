import Submission.Work.PTCert.Data.S0
import Submission.Work.PTCert.Data.Cls

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace Submission.PTCert.C
open Submission.PTCert Submission.PTCert.D

theorem kl_ok0 : classKeysOK gclT kl0 0 7229 = true := by decide +kernel
theorem kl_ok1 : classKeysOK gclT kl1 500 7229 = true := by decide +kernel
theorem kl_ok2 : classKeysOK gclT kl2 1000 7229 = true := by decide +kernel
theorem kl_ok3 : classKeysOK gclT kl3 1500 7229 = true := by decide +kernel
theorem kl_ok4 : classKeysOK gclT kl4 2000 7229 = true := by decide +kernel
theorem kl_ok5 : classKeysOK gclT kl5 2500 7229 = true := by decide +kernel
theorem kl_ok6 : classKeysOK gclT kl6 3000 7229 = true := by decide +kernel
theorem kl_ok7 : classKeysOK gclT kl7 3500 7229 = true := by decide +kernel
theorem kl_ok8 : classKeysOK gclT kl8 4000 7229 = true := by decide +kernel
theorem kl_ok9 : classKeysOK gclT kl9 4500 7229 = true := by decide +kernel
theorem kl_ok10 : classKeysOK gclT kl10 5000 7229 = true := by decide +kernel
theorem kl_ok11 : classKeysOK gclT kl11 5500 7229 = true := by decide +kernel
theorem kl_ok12 : classKeysOK gclT kl12 6000 7229 = true := by decide +kernel
theorem kl_ok13 : classKeysOK gclT kl13 6500 7229 = true := by decide +kernel
theorem kl_ok14 : classKeysOK gclT kl14 7000 7229 = true := by decide +kernel
theorem tl_ok0 : classKeysOK tclT tl0 0 7229 = true := by decide +kernel
theorem tl_ok1 : classKeysOK tclT tl1 500 7229 = true := by decide +kernel
theorem tl_ok2 : classKeysOK tclT tl2 1000 7229 = true := by decide +kernel
theorem tl_ok3 : classKeysOK tclT tl3 1500 7229 = true := by decide +kernel
theorem tl_ok4 : classKeysOK tclT tl4 2000 7229 = true := by decide +kernel
theorem tl_ok5 : classKeysOK tclT tl5 2500 7229 = true := by decide +kernel
theorem tl_ok6 : classKeysOK tclT tl6 3000 7229 = true := by decide +kernel
theorem tl_ok7 : classKeysOK tclT tl7 3500 7229 = true := by decide +kernel
theorem tl_ok8 : classKeysOK tclT tl8 4000 7229 = true := by decide +kernel
theorem tl_ok9 : classKeysOK tclT tl9 4500 7229 = true := by decide +kernel
theorem tl_ok10 : classKeysOK tclT tl10 5000 7229 = true := by decide +kernel
theorem tl_ok11 : classKeysOK tclT tl11 5500 7229 = true := by decide +kernel
theorem tl_ok12 : classKeysOK tclT tl12 6000 7229 = true := by decide +kernel
theorem tl_ok13 : classKeysOK tclT tl13 6500 7229 = true := by decide +kernel
theorem tl_ok14 : classKeysOK tclT tl14 7000 7229 = true := by decide +kernel

end Submission.PTCert.C
end
