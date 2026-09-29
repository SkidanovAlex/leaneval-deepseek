import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.basic
import Submission.Work.Params.qall
import Submission.Work.Params.nt1

namespace Work.Params

open HvdH

theorem PrimeDvdFfacOfDvdMulSub {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b < D) {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ Ffac * (b - a)) : p ∣ Ffac := by
  rcases hp.dvd_mul.mp h with h1 | h2
  · exact h1
  · -- `p ∣ b - a` and `1 ≤ b - a < D`, so `p ≤ b - a ≤ D - 1` and hence `p ∣ (D-1)! = Ffac`.
    have hD : D = 1729 := rfl
    have hle : b - a ≤ D - 1 := by rw [hD] at hb ⊢; omega
    have hpba : p ≤ b - a := Nat.le_of_dvd (Nat.sub_pos_of_lt hab) h2
    exact dvd_Ffac_of_le hp.pos (le_trans hpba hle)

end Work.Params
