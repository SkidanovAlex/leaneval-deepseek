import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.MulDefs

/-! `intCastPi` commutes with the product `mulVec` of coefficient vectors. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

theorem intCastPi_mulVec {a b d n : ℕ} (A : Mon a n → ℤ) (B : Mon b n → ℤ) :
    intCastPi (mulVec a b d A B)
      = mulVec a b d (fun m => (A m : ℝ)) (fun m => (B m : ℝ)) := by
  ext M
  simp only [mulVec, intCastPi_apply]
  push_cast
  rfl

end Work.HP.Vero
