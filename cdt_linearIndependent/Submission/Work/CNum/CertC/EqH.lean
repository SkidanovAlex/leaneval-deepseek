import Submission.Work.CNum.CertC.Lit

/-! # `Work.CNum.CertC.EqH` — cheap chunk of the tabulated certificate (GvT = literal) -/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `GvT` values on arcs 896–1023 equal the tabulated `Gv` literals. -/
theorem EqH : ((List.range 128).all (fun j => decide (GvT (896 + j) = gvLitL0.getD (896 + j) 0))) = true := by
  decide +kernel

theorem EqHv (j : ℕ) (hj : j < 128) : GvT (896 + j) = gvLitL0.getD (896 + j) 0 :=
  all_range_iff.mp EqH j hj

end Work.CNum
