/-
# ZeroFreeTables — Table8CertPrinted

The rational certificate for HB Table 8 at its **printed** entries (see
`CertData.lean`, `t8certRowsP`): for every row, HB Lemma 9.1's side condition (9.12)
holds and the left hand side of (9.13) is strictly negative, both decided by
kernel arithmetic (`norm_num`) on rational literals.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Engine

namespace Work.ZeroFreeTables

theorem Table8CertPrinted : ∀ r ∈ Work.ZeroFreeTables.t8certRowsP,
    Work.ZeroFreeTables.cond913 r.2.1 r.2.2.1 r.2.2.2 (Work.ZeroFreeTables.Kaff r.2.1) ∧
    Work.ZeroFreeTables.p913 r.2.1 r.2.2.1 r.2.2.2 (Work.ZeroFreeTables.Kaff r.2.1) < 0 := by
  intro r hr
  fin_cases hr <;>
    (constructor <;> norm_num [cond913, p913, Kaff, P3R, psi13, Kond])

end Work.ZeroFreeTables
