import Submission.CertPsiTab
import Submission.CertArith
import Submission.CertJTabsSpecP7

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The `J`-kernel table `psiTab` for `N ∈ [0, 3). -/

namespace Commons.NumberTheory.MaynardSieve

theorem psiTabSpec_0 :
    (List.range 3).all (fun d => (List.range 51).all (fun L =>
      decide (psiTab.getD ((0 + d) * 51 + L) 0
        = ∑ jj ∈ Finset.range ((0 + d) + 1), certJPsiTermN (0 + d) L jj))) = true := by
  decide

end Commons.NumberTheory.MaynardSieve
