import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqD` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 384–511 equal the tabulated `Gv` literals. -/
theorem EqD : ((List.range 128).all (fun j => decide (GvT (384 + j) = gvLitL0.getD (384 + j) 0))) = true := by
  decide +kernel

theorem EqDv (j : ℕ) (hj : j < 128) : GvT (384 + j) = gvLitL0.getD (384 + j) 0 :=
  all_range_iff.mp EqD j hj

end Work.CNum
