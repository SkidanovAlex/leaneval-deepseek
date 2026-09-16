import Submission.CertSsumData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-!
# The row function of the `Ssum` table

`ssumRowOf p'` is the packed-DP row of the row-owner signature `p'.1`, evaluated at every
certificate state: the value `unpack (packedRow (mult p'.1)) (mult p.1)` for `p ∈ cSigs`.
The literal table `ssumTableL` (`Submission/CertSsumData.lean`) is correct in that its `i`-th
entry is `ssumRowOf (cSigs[i])`; this is verified `16` rows at a time in
`Submission/CertSsumRow0` … `Submission.CertSsumRow16` and assembled in
`Submission/CertSsumAll.lean`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The packed-DP row of a row-owner signature, at all certificate states. -/
def ssumRowOf (p' : List ℕ × List ℤ) : List ℕ :=
  cSigs.map (fun p => unpack (packedRow (mult p'.1)) (mult p.1))

/-- The junk default element of `cSigs`. -/
def cNil : List ℕ × List ℤ := ([], [])

theorem ssumTableL_length : ssumTableL.length = 272 := by decide

theorem cSigs_length : cSigs.length = 272 := by decide

end Commons.NumberTheory.MaynardSieve
