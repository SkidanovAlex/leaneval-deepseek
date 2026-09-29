import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.DnB` — cheap chunk of the tabulated certificate (lower bound for gvT) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `gvT` values on arcs 128–255 are above `LOG1E13LB`. -/
theorem DnB : ((List.range 128).all (fun j => decide (LOG1E13LB ≤ gvT (128 + j)))) = true := by
  decide +kernel

theorem DnBv (j : ℕ) (hj : j < 128) : LOG1E13LB ≤ gvT (128 + j) :=
  all_range_iff.mp DnB j hj

end Work.CNum
