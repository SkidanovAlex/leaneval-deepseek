import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.defect1_mul_Uval
import Submission.Work.LinnikBurgess.defect2_mul_Uval_sq
import Submission.Work.LinnikBurgess.val_dvd_iff_castHom_eq_zero
import Submission.Work.LinnikBurgess.u8three.transfer_three

namespace Work.LinnikBurgess.lfSmall

/-- The support transfer at `p = 3`, in the `lfSmall` route.

This is exactly `Work.LinnikBurgess.u8three.transfer_three` (proved there by specialising
`Work.LinnikBurgess.bval_transfer` to `p = 3`, replacing the two arithmetic side conditions that
carry a `5 ≤ p` hypothesis by their `p = 3` counterparts), re-stated under the name the `lfSmall`
route imports. -/
theorem transfer_three {e : ℕ} (he : 2 ≤ e) (a b : Fin 3 → ℕ) : SuppTransfer 3 e a b :=
  u8three.transfer_three he a b

end Work.LinnikBurgess.lfSmall
