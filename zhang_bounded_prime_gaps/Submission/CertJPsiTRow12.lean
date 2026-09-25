import Submission.CertJPsiTabT
import Submission.CertJLookup
import Submission.CertArith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! Rows 48–50 of the transposed `J`-kernel table, against the kernel sum. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Rows `48 … 50` of the transposed table (each module checks only its own rows). -/
theorem psiTabTN_row_12 : ∀ l < 3, nthDl psiTabTN (48 + l) [] =
    (List.range 54).map (fun N => ∑ jj ∈ Finset.range (N + 1), certJPsiTermN N (48 + l) jj) := by
  decide +kernel

end Commons.NumberTheory.MaynardSieve
