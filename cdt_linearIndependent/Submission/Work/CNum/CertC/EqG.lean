import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqG` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 768–895 equal the tabulated `Gv` literals. -/
theorem EqG : ((List.range 128).all (fun j => decide (GvT (768 + j) = gvLitL0.getD (768 + j) 0))) = true := by
  decide +kernel

theorem EqGv (j : ℕ) (hj : j < 128) : GvT (768 + j) = gvLitL0.getD (768 + j) 0 :=
  all_range_iff.mp EqG j hj

end Work.CNum
