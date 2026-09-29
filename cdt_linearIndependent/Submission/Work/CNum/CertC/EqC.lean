import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqC` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 256–383 equal the tabulated `Gv` literals. -/
theorem EqC : ((List.range 128).all (fun j => decide (GvT (256 + j) = gvLitL0.getD (256 + j) 0))) = true := by
  decide +kernel

theorem EqCv (j : ℕ) (hj : j < 128) : GvT (256 + j) = gvLitL0.getD (256 + j) 0 :=
  all_range_iff.mp EqC j hj

end Work.CNum
