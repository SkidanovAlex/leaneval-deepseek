import Mathlib
import Submission.Work.BSW.Cases.Order.Setup

namespace Work.BSW.Cases.Order

theorem arithRelA {k d R : ℕ} (hk : 0 < k) (hd : 0 < d)
    (h : (k : ℂ) = ((R : ℂ) / (2 * (k : ℂ))) * (1 + 4 / (d : ℂ) - 1 / ((d : ℂ) + 1))) :
    R * (d + 2) ^ 2 = 2 * k ^ 2 * d * (d + 1) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hd1C : (d : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero d
  have h2kC : (2 * (k : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hkC
  -- Clear denominators in `h`: `1 + 4/d - 1/(d+1) = (d+2)^2 / (d*(d+1))`.
  have hc : (2 : ℂ) * (k : ℂ) ^ 2 * (d : ℂ) * ((d : ℂ) + 1)
      = (R : ℂ) * ((d : ℂ) + 2) ^ 2 := by
    field_simp at h
    ring_nf at h ⊢
    linear_combination h
  -- Transfer the complex identity back to `ℕ`.
  have hnat : 2 * k ^ 2 * d * (d + 1) = R * (d + 2) ^ 2 := by
    exact_mod_cast hc
  exact hnat.symm

end Work.BSW.Cases.Order
