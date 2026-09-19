import Submission.CertArith
import Submission.CertJData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The `Ψ`-kernel of the `J`-form, as a function of `(N,L) = (ã+ã', |β|+|β'|)`

`certJPsiND N L` is the `Ψ`-sum `∑_{jj ≤ N} certJPsiTermN N L jj` of the certificate's `J`-form.
It is defined here (rather than in the bridge module) so that its table identity can be proved
in a memory-light module.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The `Ψ`-kernel of a pair of marginal terms. -/
def certJPsiND (N L : ℕ) : ℕ :=
  ∑ jj ∈ Finset.range (N + 1), certJPsiTermN N L jj

end Commons.NumberTheory.MaynardSieve
