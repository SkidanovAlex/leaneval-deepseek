import Mathlib

namespace Work.IntLib

theorem loopCounterArith (b k N : ℕ) (hb : 1 ≤ b) :
    ((k + 1) % b = 0 → (k + 1) / b = k / b + 1) ∧
    ((k + 1) % b ≠ 0 → (k + 1) / b = k / b) ∧
    (N - (k + 1) / b = 0 ↔ b * N ≤ k + 1) ∧
    ((N - k / b) - 1 = N - (k / b + 1)) ∧
    (k < b * N → (k + 1) % b = 0 → 1 ≤ N - k / b) ∧
    ((k + 1) % b ≠ 0 → N - k / b = N - (k + 1) / b) := by
  have hb0 : 0 < b := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Nat.succ_div]
    simp [Nat.dvd_iff_mod_eq_zero, h]
  · intro h
    rw [Nat.succ_div]
    simp [Nat.dvd_iff_mod_eq_zero, h]
  · rw [Nat.sub_eq_zero_iff_le, Nat.le_div_iff_mul_le hb0, Nat.mul_comm N b]
  · exact Nat.sub_sub N (k / b) 1
  · intro hk h
    have hq : (k + 1) / b = k / b + 1 := by
      rw [Nat.succ_div]
      simp [Nat.dvd_iff_mod_eq_zero, h]
    have hle : (k + 1) / b ≤ N :=
      Nat.le_of_mul_le_mul_left
        (le_trans (Nat.mul_div_le (k + 1) b) (Nat.succ_le_of_lt hk)) hb0
    have hle' : k / b + 1 ≤ N := hq ▸ hle
    exact (Nat.le_sub_iff_add_le' (Nat.le_of_succ_le hle')).mpr hle'
  · intro h
    have hq : (k + 1) / b = k / b := by
      rw [Nat.succ_div]
      simp [Nat.dvd_iff_mod_eq_zero, h]
    rw [hq]

end Work.IntLib
