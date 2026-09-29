import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.DnC` — cheap chunk of the tabulated certificate (lower bound for gvT) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `gvT` values on arcs 256–383 are above `LOG1E13LB`. -/
theorem DnC : ((List.range 128).all (fun j => decide (LOG1E13LB ≤ gvT (256 + j)))) = true := by
  decide +kernel

theorem DnCv (j : ℕ) (hj : j < 128) : LOG1E13LB ≤ gvT (256 + j) :=
  all_range_iff.mp DnC j hj

end Work.CNum
