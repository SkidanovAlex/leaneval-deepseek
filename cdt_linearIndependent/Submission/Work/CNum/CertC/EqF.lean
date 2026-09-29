import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqF` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 640–767 equal the tabulated `Gv` literals. -/
theorem EqF : ((List.range 128).all (fun j => decide (GvT (640 + j) = gvLitL0.getD (640 + j) 0))) = true := by
  decide +kernel

theorem EqFv (j : ℕ) (hj : j < 128) : GvT (640 + j) = gvLitL0.getD (640 + j) 0 :=
  all_range_iff.mp EqF j hj

end Work.CNum
