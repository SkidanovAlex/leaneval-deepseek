import Mathlib
import Submission.Work.LinnikBurgess.lf_defs

namespace Work.LinnikBurgess

/-- For `x : ZMod (p ^ e)` and `p ^ k ∣ p ^ e`, the integer representative `x.val` is divisible by
`p ^ k` exactly when `x` dies in `ZMod (p ^ k)`. -/
theorem val_dvd_iff_castHom_eq_zero {p e k : ℕ} [Fact p.Prime] (h : p ^ k ∣ p ^ e)
    (x : ZMod (p ^ e)) :
    (p ^ k ∣ x.val) ↔ ZMod.castHom h (ZMod (p ^ k)) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

end Work.LinnikBurgess
