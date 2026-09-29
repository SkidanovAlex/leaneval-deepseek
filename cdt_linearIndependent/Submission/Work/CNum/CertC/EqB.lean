import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqB` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 128–255 equal the tabulated `Gv` literals. -/
theorem EqB : ((List.range 128).all (fun j => decide (GvT (128 + j) = gvLitL0.getD (128 + j) 0))) = true := by
  decide +kernel

theorem EqBv (j : ℕ) (hj : j < 128) : GvT (128 + j) = gvLitL0.getD (128 + j) 0 :=
  all_range_iff.mp EqB j hj

end Work.CNum
