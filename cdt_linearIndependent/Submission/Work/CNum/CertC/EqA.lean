import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqA` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 0–127 equal the tabulated `Gv` literals. -/
theorem EqA : ((List.range 128).all (fun j => decide (GvT (0 + j) = gvLitL0.getD (0 + j) 0))) = true := by
  decide +kernel

theorem EqAv (j : ℕ) (hj : j < 128) : GvT (0 + j) = gvLitL0.getD (0 + j) 0 :=
  all_range_iff.mp EqA j hj

end Work.CNum
