import Submission.Work.CNum.Cert.UpA
import Submission.Work.CNum.Cert.UpB
import Submission.Work.CNum.Cert.UpC
import Submission.Work.CNum.Cert.UpD
import Submission.Work.CNum.Cert.DnA
import Submission.Work.CNum.Cert.DnB
import Submission.Work.CNum.Cert.DnC
import Submission.Work.CNum.Cert.DnD
import Submission.Work.CNum.Cert.Cusp

namespace Work.CNum

/-- The full tabulation of `svUp` at the grid points. -/
theorem svUpTab_spec (k : ℕ) (hk : k ≤ 1024) : svUp (ptOf k) = svUpTab k := by
  by_cases h : k ≤ 255
  · exact svUpTab_specA k h
  by_cases h2 : k ≤ 511
  · exact svUpTab_specB k (by omega) h2
  by_cases h3 : k ≤ 767
  · exact svUpTab_specC k (by omega) h3
  · exact svUpTab_specD k (by omega) hk

/-- The full tabulation of `svDn` at the grid points. -/
theorem svDnTab_spec (k : ℕ) (hk : k ≤ 1024) : svDn (ptOf k) = svDnTab k := by
  by_cases h : k ≤ 255
  · exact svDnTab_specA k h
  by_cases h2 : k ≤ 511
  · exact svDnTab_specB k (by omega) h2
  by_cases h3 : k ≤ 767
  · exact svDnTab_specC k (by omega) h3
  · exact svDnTab_specD k (by omega) hk

end Work.CNum
