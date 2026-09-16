import Submission.CertChunks

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `0`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_0 : chunkI 0 = (-1845208664027598001170294963440621731628825091632788799695268444100351699511811058608551537174656364269458313875993090195347218888177130444548178549612069945328871001407139841761987722890178102625156720602487709643598385001471045262644533819271182470977945600000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
