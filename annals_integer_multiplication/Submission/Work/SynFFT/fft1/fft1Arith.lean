import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# Arithmetic facts for the slice word (`HasFFT1`)
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

theorem fft1Arith (r k t : ℕ) (hr : HvdH.IsPow2 r) (ht : t = 2 ^ k) (htr : t ∣ 2 * r) :
    (∀ i, i ≤ k → t / 2 ^ i * 2 ^ (Nat.clog 2 (2 * r) - k + i) = 2 * r) ∧
    (∀ i, i < k → 2 ≤ t / 2 ^ i) ∧
    (∀ i, i < k → 2 * 2 ^ i ∣ t) ∧
    (∀ i, i ≤ k → t / 2 ^ i / 2 = t / 2 ^ (i + 1)) ∧
    (∀ i, i < k → t / 2 ^ i ∣ t) ∧
    (0 < t) ∧ (t ≤ 2 * r) ∧ (k ≤ Nat.clog 2 (2 * r)) ∧
    (∀ i, i ≤ k → t / 2 ^ i ≤ t) ∧ (∀ i, i ≤ k → 2 ^ i ≤ t) := by
  obtain ⟨j, hj1, hrj⟩ := hr
  have h2r : 2 * r = 2 ^ (j + 1) := by
    rw [hrj, ← pow_succ']
  have hcr : Nat.clog 2 (2 * r) = j + 1 := by
    rw [h2r, Nat.clog_pow 2 (j + 1) (by norm_num)]
  have hkj : k ≤ j + 1 := by
    have h : 2 ^ k ∣ 2 ^ (j + 1) := by rw [← ht, ← h2r]; exact htr
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hexp : (k - i) + (Nat.clog 2 (2 * r) - k + i) = j + 1 := by rw [hcr]; omega
    have h1 : t / 2 ^ i = 2 ^ (k - i) := by rw [ht, Nat.pow_div hi (by norm_num)]
    rw [h1, ← pow_add, hexp, h2r]
  · intro i hi
    rw [ht, Nat.pow_div (le_of_lt hi) (by norm_num)]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro i hi
    have h2i : 2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ']
    rw [ht, h2i]
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mpr (by omega)
  · intro i hi
    rw [Nat.div_div_eq_div_mul, show 2 ^ i * 2 = 2 ^ (i + 1) by rw [pow_succ]]
  · intro i hi
    rw [ht, Nat.pow_div (le_of_lt hi) (by norm_num)]
    exact Nat.pow_dvd_pow 2 (by omega)
  · rw [ht]; positivity
  · rw [ht, h2r]
    exact Nat.pow_le_pow_right (by norm_num) hkj
  · rw [hcr]; omega
  · intro i hi; exact Nat.div_le_self _ _
  · intro i hi
    rw [ht]
    exact Nat.pow_le_pow_right (by norm_num) hi

end Work.SynFFT
