import Mathlib

namespace Work.SG

/-- For integers `a`, `b`, the square of `a - b` equals `0` when `a` and `b` have the
same parity and `1` otherwise, exactly when `a` and `b` differ by at most `1`. -/
theorem parity_sq_eq_iff (a b : ℤ) :
    (a - b) ^ 2 = (if a % 2 = b % 2 then 0 else 1) ↔ |a - b| ≤ 1 := by
  have hpar : (a % 2 = b % 2) ↔ (a - b) % 2 = 0 := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  simp only [hpar]
  set d := a - b with hd
  constructor
  · intro h
    rw [abs_le]
    by_cases h2 : d % 2 = 0
    · rw [ite_eq_left h2] at h
      have hd0 : d = 0 := sq_eq_zero_iff.mp h
      omega
    · rw [ite_eq_right h2] at h
      have h1 : d ^ 2 = (1 : ℤ) ^ 2 := by rw [h]; norm_num
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h' | h' <;> omega
  · intro h
    rw [abs_le] at h
    obtain ⟨h1, h2⟩ := h
    have hd : d = -1 ∨ d = 0 ∨ d = 1 := by omega
    rcases hd with hh | hh | hh
    · rw [hh]; norm_num
    · rw [hh]; norm_num
    · rw [hh]; norm_num

end Work.SG
