import Submission.CertJPsiTabT
import Submission.CertJLookup
import Submission.CertArith
import Submission.CertJPsiTRow7

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! Rows 32–35 of the transposed `J`-kernel table, against the kernel sum. -/

namespace Commons.NumberTheory.MaynardSieve

theorem psiTabTN_row_8 : ∀ L < 36, nthDl psiTabTN L [] =
    (List.range 54).map (fun N => ∑ jj ∈ Finset.range (N + 1), certJPsiTermN N L jj) := by decide

end Commons.NumberTheory.MaynardSieve
