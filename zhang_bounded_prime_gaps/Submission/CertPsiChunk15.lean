import Submission.CertPsiTab
-- Build-order chain only: at most 3 `psiTab` slice modules build at once.
import Submission.CertPsiChunk12
import Submission.CertArith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The `J`-kernel table `psiTab` for `N ∈ [45, 48). -/

namespace Commons.NumberTheory.MaynardSieve

/-- Entries `153·15 … 153·15+152` of `psiTab` (`N ∈ [45, 48)`, all `L ≤ 50`), checked as one
slice so that the literal is walked once. -/
theorem psiTabSlice_15 : (psiTab.drop (153 * 15)).take 153
    = (List.range 153).map (fun t => ∑ jj ∈ Finset.range ((3 * 15 + t / 51) + 1),
        certJPsiTermN (3 * 15 + t / 51) (t % 51) jj) := by
  decide +kernel

end Commons.NumberTheory.MaynardSieve
