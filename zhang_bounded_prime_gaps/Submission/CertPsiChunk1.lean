import Submission.CertPsiTab
import Submission.CertArith
import Submission.CertPsiChunk0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-! The `J`-kernel table `psiTab` for `N ∈ [3, 6). -/

namespace Commons.NumberTheory.MaynardSieve

theorem psiTabSpec_1 :
    (List.range 3).all (fun d => (List.range 51).all (fun L =>
      decide (psiTab.getD ((3 + d) * 51 + L) 0
        = ∑ jj ∈ Finset.range ((3 + d) + 1), certJPsiTermN (3 + d) L jj))) = true := by
  decide

end Commons.NumberTheory.MaynardSieve
