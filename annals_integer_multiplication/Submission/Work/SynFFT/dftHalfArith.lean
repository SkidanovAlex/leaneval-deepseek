import Mathlib
import Submission.Work.SynFFT.defs

namespace Work.SynFFT

theorem dftHalfArith (r t : ℕ) (hr : 0 < r) (ht : ∃ k : ℕ, 1 ≤ k ∧ t = 2 ^ k) (htr : t ∣ 2 * r) :
    2 ≤ t ∧ 0 < t / 2 ∧ 2 * (t / 2) = t ∧ (t / 2) ∣ 2 * r ∧
    (2 * r / (t / 2) = 2 * (2 * r / t)) ∧ (2 * r / t) * (t / 2) = r ∧ 0 < 2 * r / t := by
  obtain ⟨k, hk1, rfl⟩ := ht
  have hk0 : 0 < k := by omega
  -- t = 2^k is twice 2^(k-1)
  have ht_eq : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_pred_mul (x := 2) (w := k) hk0, mul_comm]
  have hdiv : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rw [ht_eq, Nat.mul_div_right _ (show 0 < 2 by norm_num)]
  have hpos : 0 < 2 ^ (k - 1) := Nat.two_pow_pos _
  have h2pos : 0 < 2 * 2 ^ (k - 1) := Nat.mul_pos (by norm_num) hpos
  -- 2^(k-1) divides r
  have hmdvd : 2 ^ (k - 1) ∣ r := by
    rw [ht_eq] at htr
    exact (Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)).mp htr
  obtain ⟨q, hq⟩ := hmdvd
  subst hq
  rw [hdiv, ht_eq]
  refine ⟨?_, hpos, rfl, ?_, ?_, ?_, ?_⟩
  · omega
  · exact ⟨2 * q, by ring⟩
  · have hL : 2 * (2 ^ (k - 1) * q) / 2 ^ (k - 1) = 2 * q := by
      have h1 : 2 * (2 ^ (k - 1) * q) = 2 ^ (k - 1) * (2 * q) := by ring
      rw [h1, Nat.mul_div_cancel_left (2 * q) hpos]
    have hR : 2 * (2 * (2 ^ (k - 1) * q) / (2 * 2 ^ (k - 1))) = 2 * q := by
      have h2 : 2 * (2 ^ (k - 1) * q) = (2 * 2 ^ (k - 1)) * q := by ring
      rw [h2, Nat.mul_div_cancel_left q h2pos]
    exact hL.trans hR.symm
  · have h1 : 2 * (2 ^ (k - 1) * q) = (2 * 2 ^ (k - 1)) * q := by ring
    rw [h1, Nat.mul_div_cancel_left q h2pos]
    ring
  · have h1 : 2 * (2 ^ (k - 1) * q) = (2 * 2 ^ (k - 1)) * q := by ring
    rw [h1, Nat.mul_div_cancel_left q h2pos]
    exact Nat.pos_of_mul_pos_left hr

end Work.SynFFT
