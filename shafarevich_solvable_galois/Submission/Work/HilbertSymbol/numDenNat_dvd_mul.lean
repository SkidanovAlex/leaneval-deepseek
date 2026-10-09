import Mathlib
import Submission.Work.HilbertSymbol.Places
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem numDenNat_dvd_mul (a b : ℚˣ) : numDenNat (a * b) ∣ numDenNat a * numDenNat b := by
  unfold numDenNat
  simp only [Units.val_mul]
  have hden : ((a : ℚ) * (b : ℚ)).den ∣ (a : ℚ).den * (b : ℚ).den := Rat.mul_den_dvd _ _
  have hnum : ((a : ℚ) * (b : ℚ)).num.natAbs ∣ (a : ℚ).num.natAbs * (b : ℚ).num.natAbs := by
    have h := Rat.num_mul_num_eq_num_mul_gcd (a : ℚ) (b : ℚ)
    have hdvd : ((a : ℚ) * (b : ℚ)).num ∣ (a : ℚ).num * (b : ℚ).num := by
      rw [h]; exact dvd_mul_right _ _
    have h' := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_mul] at h'
  have := Nat.mul_dvd_mul hnum hden
  simpa [mul_assoc, mul_comm, mul_left_comm] using this

end Work.HilbertSymbol
