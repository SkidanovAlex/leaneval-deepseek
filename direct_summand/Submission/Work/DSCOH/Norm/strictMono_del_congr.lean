import Mathlib
import Submission.Work.DSCOH.Norm.Defs
import Submission.Work.DSCOH.Norm.del_eq_of_monotone_of_eq

namespace Work.DSCOH.Norm

universe w

/-- Deleting a repeated entry of a nondecreasing tuple does not depend on which of the two
positions is deleted, so strict monotonicity of the deletion is the same for both positions. -/
theorem strictMono_del_congr {ι : Type w} [LinearOrder ι] {n : ℕ} {x : Fin (n + 2) → ι}
    (hx : Monotone x) {b b' : Fin (n + 2)} (hbb' : b ≠ b') (h : x b = x b') :
    (StrictMono (Work.DSCOH.Norm.del x b) ↔ StrictMono (Work.DSCOH.Norm.del x b')) := by
  rw [del_eq_of_monotone_of_eq hx h]

end Work.DSCOH.Norm
