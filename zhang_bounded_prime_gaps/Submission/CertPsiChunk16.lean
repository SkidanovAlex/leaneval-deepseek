import Submission.CertPsiTab
-- Build-order chain only: at most 3 `psiTab` slice modules build at once.
import Submission.CertPsiChunk13
import Submission.CertArith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The `J`-kernel table `psiTab` for `N ∈ [48, 51). -/

namespace Commons.NumberTheory.MaynardSieve

/-- Entries `153·16 … 153·16+152` of `psiTab` (`N ∈ [48, 51)`, all `L ≤ 50`), checked as one
slice so that the literal is walked once. -/
theorem psiTabSlice_16 : (psiTab.drop (153 * 16)).take 153
    = (List.range 153).map (fun t => ∑ jj ∈ Finset.range ((3 * 16 + t / 51) + 1),
        certJPsiTermN (3 * 16 + t / 51) (t % 51) jj) := by
  decide +kernel

end Commons.NumberTheory.MaynardSieve
