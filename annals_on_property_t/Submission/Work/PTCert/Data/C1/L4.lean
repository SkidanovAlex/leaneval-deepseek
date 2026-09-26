import Submission.Work.PTCert.KernelCert
import Submission.Work.PTCert.Data.C1.L4_0
import Submission.Work.PTCert.Data.C1.L4_1
import Submission.Work.PTCert.Data.C1.L4_2
import Submission.Work.PTCert.Data.C1.L4_3

set_option maxRecDepth 100000
noncomputable section
namespace Submission.PTCert.D1
open Submission.PTCert

def Cs4 : List (List (List ℤ)) := [C4_0, C4_1, C4_2, C4_3]
def Ws4 : List (List ℤ) := [W4_0, W4_1, W4_2, W4_3]

end Submission.PTCert.D1
end
