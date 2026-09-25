import Submission.CertJPsiTabT
import Submission.CertJLookup
import Submission.CertArith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! Rows 12–15 of the transposed `J`-kernel table, against the kernel sum. -/

namespace Commons.NumberTheory.MaynardSieve

/-- Rows `12 … 15` of the transposed table (each module checks only its own rows). -/
theorem psiTabTN_row_3 : ∀ l < 4, nthDl psiTabTN (12 + l) [] =
    (List.range 54).map (fun N => ∑ jj ∈ Finset.range (N + 1), certJPsiTermN N (12 + l) jj) := by
  decide +kernel

end Commons.NumberTheory.MaynardSieve
