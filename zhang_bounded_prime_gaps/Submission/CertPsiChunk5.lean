import Submission.CertPsiTab
import Submission.CertArith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The `J`-kernel table `psiTab` for `N ∈ [15, 18). -/

namespace Commons.NumberTheory.MaynardSieve

theorem psiTabSpec_5 :
    (List.range 3).all (fun d => (List.range 51).all (fun L =>
      decide (psiTab.getD ((15 + d) * 51 + L) 0
        = ∑ jj ∈ Finset.range ((15 + d) + 1), certJPsiTermN (15 + d) L jj))) = true := by
  decide

end Commons.NumberTheory.MaynardSieve
