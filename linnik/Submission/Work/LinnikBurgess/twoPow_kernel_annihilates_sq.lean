import Mathlib

namespace Work.LinnikBurgess

/-- In `ZMod (2 ^ K)`, if `h` is annihilated by `2 ^ g` and `g + 1 ≤ K`, then `h ^ 2` is
annihilated by `2 ^ (g - 1)`:  `h ∈ ker(2 ^ g) = 2 ^ (K - g) · ZMod (2 ^ K)`, so
`2 ^ (g - 1) · h ^ 2 ∈ 2 ^ (g - 1) · 2 ^ (2K - 2g) · ZMod (2 ^ K) = 2 ^ (2K - g - 1) · ZMod (2 ^ K)`,
which is `0` because `2K - g - 1 ≥ K`. -/
theorem twoPow_kernel_annihilates_sq {K g : ℕ} (hg1 : 1 ≤ g) (hgK : g + 1 ≤ K)
    {h : ZMod (2 ^ K)} (hh : ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0) :
    ((2 ^ (g - 1) : ℕ) : ZMod (2 ^ K)) * h ^ 2 = 0 := by
  -- `g ≤ K`, hence the modulus `2 ^ K` factors as `2 ^ g * 2 ^ (K - g)`.
  have hgK' : g ≤ K := by omega
  -- Rewriting the hypothesis `2 ^ g * h = 0` in `ZMod (2 ^ K)` as a divisibility
  -- statement about the canonical representative `h.val ∈ {0, …, 2 ^ K - 1}`.
  have key : ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = ((2 ^ g * h.val : ℕ) : ZMod (2 ^ K)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val h]
  have hdvd : 2 ^ K ∣ 2 ^ g * h.val := by
    rw [key] at hh
    exact (ZMod.natCast_eq_zero_iff (2 ^ g * h.val) (2 ^ K)).mp hh
  have hpow : 2 ^ K = 2 ^ g * 2 ^ (K - g) := by
    rw [← pow_add, Nat.add_sub_cancel' hgK']
  -- Cancelling the common factor `2 ^ g`.
  have hdvd2 : 2 ^ (K - g) ∣ h.val := by
    have h' : 2 ^ g * 2 ^ (K - g) ∣ 2 ^ g * h.val := by rwa [← hpow]
    exact (Nat.mul_dvd_mul_iff_left (a := 2 ^ g) (b := 2 ^ (K - g)) (c := h.val)
      (by positivity : 0 < 2 ^ g)).mp h'
  -- The arithmetic core: `2 ^ K ∣ 2 ^ (g - 1) * h.val ^ 2`.
  have harith : 2 ^ K ∣ 2 ^ (g - 1) * h.val ^ 2 := by
    obtain ⟨q, hq⟩ := hdvd2
    rw [hq]
    have h1 : (2 ^ (K - g) * q) ^ 2 = 2 ^ (2 * (K - g)) * q ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (K - g) 2]
    rw [h1, ← mul_assoc, ← pow_add]
    have hle : K ≤ (g - 1) + 2 * (K - g) := by omega
    exact (pow_dvd_pow (2 : ℕ) hle).trans (dvd_mul_right _ _)
  -- Transfer the divisibility back into `ZMod (2 ^ K)`.
  have hh2 : ((2 ^ (g - 1) : ℕ) : ZMod (2 ^ K)) * h ^ 2
      = ((2 ^ (g - 1) * h.val ^ 2 : ℕ) : ZMod (2 ^ K)) := by
    push_cast
    rw [ZMod.natCast_zmod_val h]
  rw [hh2]
  exact (ZMod.natCast_eq_zero_iff (2 ^ (g - 1) * h.val ^ 2) (2 ^ K)).mpr harith

end Work.LinnikBurgess
