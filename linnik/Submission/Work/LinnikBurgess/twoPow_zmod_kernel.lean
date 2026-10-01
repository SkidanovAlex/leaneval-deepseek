import Mathlib

namespace Work.LinnikBurgess

theorem twoPow_zmod_kernel {K j : ℕ} (hj : j ≤ K) (h : ZMod (2 ^ K)) :
    ((((2 ^ j : ℕ) : ZMod (2 ^ K)) * h = 0) ↔ 2 ^ (K - j) ∣ h.val) ∧
    ((((2 ^ j : ℕ) : ZMod (2 ^ K)) * h = 0) →
      ∃ t : ZMod (2 ^ K), h = ((2 ^ (K - j) : ℕ) : ZMod (2 ^ K)) * t) := by
  have key : ((2 ^ j : ℕ) : ZMod (2 ^ K)) * h = ((2 ^ j * h.val : ℕ) : ZMod (2 ^ K)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val h]
  have hpow : 2 ^ K = 2 ^ j * 2 ^ (K - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  have hdmul : (2 ^ K ∣ 2 ^ j * h.val) ↔ (2 ^ (K - j) ∣ h.val) := by
    have hstep := Nat.mul_dvd_mul_iff_left (a := 2 ^ j) (b := 2 ^ (K - j))
      (c := h.val) (by positivity : 0 < 2 ^ j)
    rwa [← hpow] at hstep
  have hiff : ((2 ^ j : ℕ) : ZMod (2 ^ K)) * h = 0 ↔ 2 ^ (K - j) ∣ h.val := by
    rw [key, ZMod.natCast_eq_zero_iff]
    exact hdmul
  refine ⟨hiff, ?_⟩
  intro h0
  have hdvd : 2 ^ (K - j) ∣ h.val := hiff.mp h0
  refine ⟨((h.val / 2 ^ (K - j) : ℕ) : ZMod (2 ^ K)), ?_⟩
  have hval : (h.val : ZMod (2 ^ K)) =
      ((2 ^ (K - j) : ℕ) : ZMod (2 ^ K)) * ((h.val / 2 ^ (K - j) : ℕ) : ZMod (2 ^ K)) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  exact (ZMod.natCast_zmod_val h).symm.trans hval

end Work.LinnikBurgess
