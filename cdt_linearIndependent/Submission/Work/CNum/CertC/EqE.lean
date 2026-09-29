import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqE` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 512–639 equal the tabulated `Gv` literals. -/
theorem EqE : ((List.range 128).all (fun j => decide (GvT (512 + j) = gvLitL0.getD (512 + j) 0))) = true := by
  decide +kernel

theorem EqEv (j : ℕ) (hj : j < 128) : GvT (512 + j) = gvLitL0.getD (512 + j) 0 :=
  all_range_iff.mp EqE j hj

end Work.CNum
