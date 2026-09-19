import Submission.CertPsiTab
import Submission.CertArith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The `J`-kernel table `psiTab` for `N ∈ [39, 42). -/

namespace Commons.NumberTheory.MaynardSieve

theorem psiTabSpec_13 :
    (List.range 3).all (fun d => (List.range 51).all (fun L =>
      decide (psiTab.getD ((39 + d) * 51 + L) 0
        = ∑ jj ∈ Finset.range ((39 + d) + 1), certJPsiTermN (39 + d) L jj))) = true := by
  decide

end Commons.NumberTheory.MaynardSieve
