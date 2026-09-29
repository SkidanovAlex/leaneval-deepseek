import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.DnF` — cheap chunk of the tabulated certificate (lower bound for gvT) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `gvT` values on arcs 640–767 are above `LOG1E13LB`. -/
theorem DnF : ((List.range 128).all (fun j => decide (LOG1E13LB ≤ gvT (640 + j)))) = true := by
  decide +kernel

theorem DnFv (j : ℕ) (hj : j < 128) : LOG1E13LB ≤ gvT (640 + j) :=
  all_range_iff.mp DnF j hj

end Work.CNum
