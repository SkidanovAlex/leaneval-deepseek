import Submission.CertSsum49Data
import Submission.CertRowFn

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-!
# The `k = 49` row function and the chunk checks of `ssumTable49L`
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The packed-DP row at level `k` of a row-owner signature, at all certificate states. -/
def ssumRowOfAt (k : ℕ) (p' : List ℕ × List ℤ) : List ℕ :=
  cSigs.map (fun p => unpack (packedRowAt k (mult p'.1)) (mult p.1))

theorem ssumRowOfAt_50 (p' : List ℕ × List ℤ) : ssumRowOfAt 50 p' = ssumRowOf p' := rfl

theorem ssumTable49L_length : ssumTable49L.length = 272 := by decide

theorem cSigs_length49 : cSigs.length = 272 := by decide

end Commons.NumberTheory.MaynardSieve
