import Mathlib

namespace Work.SG

/-- If `2 ∣ c - a` then `c` and `a` have the same parity (as integers). -/
lemma emod_two_eq_of_dvd_sub {a c : ℤ} (h : (2 : ℤ) ∣ c - a) : c % 2 = a % 2 := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact (Int.dvd_iff_emod_eq_zero).mp h

theorem parity_sq_le (a b c d : ℤ) (h1 : (2 : ℤ) ∣ c - a) (h2 : (2 : ℤ) ∣ d - b) :
    (if a % 2 = b % 2 then 0 else 1) ≤ (c - d) ^ 2 := by
  have hc : c % 2 = a % 2 := emod_two_eq_of_dvd_sub h1
  have hd : d % 2 = b % 2 := emod_two_eq_of_dvd_sub h2
  by_cases hab : a % 2 = b % 2
  · rw [ite_eq_left hab]
    exact sq_nonneg _
  · rw [ite_eq_right hab]
    have hcd : c ≠ d := by
      intro hceq
      apply hab
      rw [← hc, hceq, hd]
    have h' : c - d ≠ 0 := sub_ne_zero.mpr hcd
    have hp : 0 < (c - d) ^ 2 := sq_pos_of_ne_zero h'
    omega

end Work.SG
