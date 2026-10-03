/-
# `Submission.Work.FIArea7CF.card_Sz_one` — clash-free copy of `Submission.Work.FIArea7.card_Sz_one`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.R2countDefs

namespace Work.FIArea7

lemma card_Sz_one : (Work.FIArea7.Sz 1).card = 4 := by
  decide

end Work.FIArea7
