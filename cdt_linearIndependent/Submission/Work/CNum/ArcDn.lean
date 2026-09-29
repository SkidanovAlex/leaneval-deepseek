import Mathlib
import Submission.Work.CNum.DAux.Main

namespace Work.CNum

theorem ArcDn (k : ℕ) (hk : k < 1024) : ∀ t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024), Work.ANum.m2r (Work.CNum.gv k) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t :=
  ArcDnMain k hk

end Work.CNum
