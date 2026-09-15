import Mathlib.Data.ZMod.Basic

namespace Commons.NumberTheory.ZMod

theorem abs_bal_eq_min {p : ℕ} [NeZero p] (z : ZMod p) :
    |(if 2 * z.val ≤ p then (z.val : ℤ) else (z.val : ℤ) - (p : ℤ))|
      = (min z.val (p - z.val) : ℤ) := by
  have hzlt : z.val < p := ZMod.val_lt z
  by_cases h : 2 * z.val ≤ p
  · have hle : z.val ≤ p - z.val := by omega
    have hle' : (z.val : ℤ) ≤ (p : ℤ) - (z.val : ℤ) := by
      have h2 : z.val + z.val ≤ p := by omega
      omega
    rw [if_pos h, abs_of_nonneg (Int.natCast_nonneg _), min_eq_left hle']
  · have hge : p - z.val ≤ z.val := by omega
    have hge' : (p : ℤ) - (z.val : ℤ) ≤ (z.val : ℤ) := by omega
    have hnonpos : (z.val : ℤ) - (p : ℤ) ≤ 0 := by omega
    rw [if_neg h, abs_of_nonpos hnonpos, min_eq_right hge']
    omega

end Commons.NumberTheory.ZMod