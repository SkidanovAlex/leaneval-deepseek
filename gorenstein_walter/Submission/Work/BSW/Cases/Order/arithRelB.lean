import Mathlib
import Submission.Work.BSW.Cases.Order.Setup

namespace Work.BSW.Cases.Order

theorem arithRelB {k d R : ℕ} (hk : 0 < k) (hd : 2 ≤ d)
    (h : (k : ℂ) = ((R : ℂ) / (2 * (k : ℂ))) * (1 + 1 / ((d : ℂ) - 1) - 4 / (d : ℂ))) :
    R * (d - 2) ^ 2 = 2 * k ^ 2 * d * (d - 1) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : d ≠ 0)
  have hd1C : (d : ℂ) - 1 ≠ 0 := by
    have hsub : (d : ℂ) - 1 = ((d - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
    rw [hsub]; exact Nat.cast_ne_zero.mpr (by omega)
  have h2kC : (2 * (k : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hkC
  -- Clear denominators: `1 + 1/(d - 1) - 4/d = (d - 2)^2 / (d * (d - 1))`.
  have hc : (2 : ℂ) * (k : ℂ) ^ 2 * (d : ℂ) * ((d : ℂ) - 1)
      = (R : ℂ) * ((d : ℂ) - 2) ^ 2 := by
    field_simp at h
    ring_nf at h ⊢
    linear_combination h
  -- Transfer the complex identity back to `ℕ`.
  have hd1 : (d : ℂ) - 1 = ((d - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
  have hd2 : (d : ℂ) - 2 = ((d - 2 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hd]; norm_num
  rw [hd1, hd2] at hc
  have hnat : 2 * k ^ 2 * d * (d - 1) = R * (d - 2) ^ 2 := by
    exact_mod_cast hc
  exact hnat.symm

end Work.BSW.Cases.Order
