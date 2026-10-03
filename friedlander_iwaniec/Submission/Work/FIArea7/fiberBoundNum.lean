import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea7

open Work

/-- `(2R+1).toNat = 2R+1` for a natural number `R`: the integer `2R+1` is non-negative, and its
`toNat` is `2R+1`. -/
private lemma toNat_two_mul_add_one (R : ℕ) : (2 * (R : ℤ) + 1).toNat = 2 * R + 1 := by
  have h : (2 * (R : ℤ) + 1) = ((2 * R + 1 : ℕ) : ℤ) := by omega
  exact (congrArg Int.toNat h).trans (Int.toNat_natCast _)

/-- **The numeric fibre count of the box `gBox (radN Pa)` modulo `Q`.**  The number of box points in
one class mod `Q` is `((2R+1)/Q + 1)^2` with `R = radN Pa = ⌈√(4N)⌉ ≤ 2√N + 1`, and
`2R+1 ≤ 4√N + 3 ≤ 7√N` for `N ≥ 1`, so `Q·((2R+1).toNat/Q + 1)^2 ≤ 200·N/Q + 4Q`. -/
theorem fiberBoundNum {Pa : Work.FITop.Params} {Q : ℕ} (hQ : 0 < Q) :
    (Q : ℝ) * ((((2 * Work.FITop.radN Pa + 1).toNat / Q + 1 : ℕ)) : ℝ) ^ 2
      ≤ 200 * Pa.N / Q + 4 * Q := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQ0
  -- `√(4N) = 2√N`
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Pa.N]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h4]
  -- the ceiling of `√(4N)` is `< 2√N + 1`
  have hceil0 : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) < Real.sqrt (4 * Pa.N) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceil : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) < 2 * Real.sqrt Pa.N + 1 := by
    linarith [hceil0, hsqrt4]
  -- `radN Pa` unfolded: its `toNat` is `⌈√(4N)⌉₊`
  have htoNat : (2 * Work.FITop.radN Pa + 1).toNat = 2 * (⌈Real.sqrt (4 * Pa.N)⌉₊) + 1 := by
    rw [Work.FITop.radN]
    exact toNat_two_mul_add_one _
  rw [htoNat]
  set a : ℕ := 2 * ⌈Real.sqrt (4 * Pa.N)⌉₊ + 1 with ha
  have hs1 : (1 : ℝ) ≤ Real.sqrt Pa.N := by
    rw [Real.one_le_sqrt]; exact hN1
  -- `a ≤ 7√N`
  have ha_bound : (a : ℝ) ≤ 7 * Real.sqrt Pa.N := by
    rw [ha]; push_cast; linarith
  -- `a² ≤ 49N`
  have ha_sq : (a : ℝ) ^ 2 ≤ 49 * Pa.N := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    have hs2 : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt hN0
    have h : (a : ℝ) * a ≤ (7 * Real.sqrt Pa.N) * (7 * Real.sqrt Pa.N) :=
      mul_le_mul ha_bound ha_bound ha0 (by positivity)
    nlinarith [h, hs2]
  -- the loss of the integer division is at most one unit: `⌊a/Q⌋ + 1 ≤ (a+Q)/Q`
  have hstepA : (((a / Q + 1 : ℕ)) : ℝ) ≤ (((a : ℝ) + Q) / Q) := by
    have h1 : (((a / Q : ℕ)) : ℝ) ≤ (a : ℝ) / Q := Nat.cast_div_le
    have h2 : (((a : ℝ) + Q) / Q) = (a : ℝ) / Q + 1 := by rw [add_div, div_self hQne]
    have h3 : (((a / Q + 1 : ℕ)) : ℝ) = (((a / Q : ℕ)) : ℝ) + 1 := by push_cast; ring
    linarith
  have hstepB : (((a / Q + 1 : ℕ)) : ℝ) ^ 2 ≤ (((a : ℝ) + Q) / Q) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hstepA 2
  have hstepC : (Q : ℝ) * (((a : ℝ) + Q) / Q) ^ 2 = ((a : ℝ) + Q) ^ 2 / Q := by field_simp
  -- `(a+Q)² ≤ 200N + 4Q²` (completing the square in `Q`)
  have hkey : ((a : ℝ) + Q) ^ 2 ≤ 200 * Pa.N + 4 * Q ^ 2 := by
    have h1 : ((a : ℝ) + Q) ^ 2 ≤ 4 / 3 * (a : ℝ) ^ 2 + 4 * Q ^ 2 := by
      nlinarith [sq_nonneg ((a : ℝ) - 3 * Q)]
    have h2 : 4 / 3 * (a : ℝ) ^ 2 ≤ 200 * Pa.N := by nlinarith [ha_sq, hN0]
    linarith
  have hstepE : ((a : ℝ) + Q) ^ 2 / Q ≤ 200 * Pa.N / Q + 4 * Q := by
    have h := div_le_div_of_nonneg_right hkey hQ0.le
    have hsplit : (200 * Pa.N + 4 * Q ^ 2) / Q = 200 * Pa.N / Q + 4 * Q := by field_simp
    linarith
  calc (Q : ℝ) * (((a / Q + 1 : ℕ)) : ℝ) ^ 2
      ≤ (Q : ℝ) * (((a : ℝ) + Q) / Q) ^ 2 := mul_le_mul_of_nonneg_left hstepB hQ0.le
    _ = ((a : ℝ) + Q) ^ 2 / Q := hstepC
    _ ≤ 200 * Pa.N / Q + 4 * Q := hstepE

end Work.FIArea7
