import Mathlib

namespace Work.KMTAreas.A7

/-- For `x ≥ 1`, the base-`2` logarithm of `x` is at most `x`.  (Proof: with `n = ⌊x⌋₊`,
`x < n + 1 ≤ 2 ^ n ≤ 2 ^ x`, and `logb 2 x ≤ x ↔ x ≤ 2 ^ x`.) -/
lemma logb_two_le_self {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ x := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]
  have hxn : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have h1 : ((⌊x⌋₊ : ℝ) + 1) ≤ ((2 : ℝ) ^ ⌊x⌋₊) := by
    have h := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := ⌊x⌋₊))
    exact_mod_cast h
  have h2 : ((2 : ℝ) ^ ⌊x⌋₊) ≤ (2 : ℝ) ^ x := by
    have h : (2 : ℝ) ^ ((⌊x⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ x :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hxn
    simpa using h
  linarith

/-- Numeric core, in real form: if `c ≥ 1`, `t ≥ 2` and
`t - 1 ≤ c · logb 2 t + 2 · t^{1/4}` then `t < (4c+3)^4`.

Put `s = t^{1/4}`, so that `t = s^4`.  If `s ≥ 4c+3` then `logb 2 t = 4 logb 2 s ≤ 4s`
(using `logb 2 s ≤ s`, which holds as `s ≥ 1`), whence `s^4 - 1 ≤ (4c+2) s`, i.e.
`s^4 ≤ (4c+2) s + 1`.  Since `4c+2 ≤ s`, this gives `s^4 ≤ s^2 + 1`, contradicting `s ≥ 2`
(which yields `s^4 ≥ 4 s^2`).  Hence `s < 4c+3` and `t = s^4 < (4c+3)^4`. -/
lemma four_mul_logb_core {c t : ℝ} (hc : 1 ≤ c) (ht : 2 ≤ t)
    (h : t - 1 ≤ c * Real.logb 2 t + 2 * t ^ ((1 : ℝ) / 4)) :
    t < (4 * c + 3) ^ 4 := by
  set s : ℝ := t ^ ((1 : ℝ) / 4) with hs
  have htpos : 0 < t := by linarith
  have hs4 : s ^ 4 = t := by
    have h2 := Real.rpow_inv_natCast_pow (x := t) (n := 4) (le_of_lt htpos) (by norm_num)
    rw [show (((4 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 4 by norm_num] at h2
    simpa [s] using h2
  have hs0 : (0 : ℝ) ≤ s := by
    rw [hs]; exact Real.rpow_nonneg (le_of_lt htpos) _
  have hslt : s < 4 * c + 3 := by
    by_contra hge
    have hge' : 4 * c + 3 ≤ s := not_lt.mp hge
    have hs1 : (1 : ℝ) ≤ s := by linarith
    have hs2 : (2 : ℝ) ≤ s := by linarith
    have hlog : Real.logb 2 s ≤ s := logb_two_le_self hs1
    have hlogt : Real.logb 2 t = 4 * Real.logb 2 s := by
      rw [← hs4, Real.logb_pow]
      norm_num
    have hbound : t - 1 ≤ (4 * c + 2) * s := by
      have hc0 : (0 : ℝ) ≤ c := by linarith
      have hstep : c * Real.logb 2 t ≤ c * (4 * s) := by
        rw [hlogt]
        exact mul_le_mul_of_nonneg_left (by linarith) hc0
      calc t - 1 ≤ c * Real.logb 2 t + 2 * s := h
        _ ≤ c * (4 * s) + 2 * s := by linarith
        _ = (4 * c + 2) * s := by ring
    have h4 : s ^ 4 ≤ (4 * c + 2) * s + 1 := by
      rw [← hs4] at hbound
      linarith
    have hC : 4 * c + 2 ≤ s := by linarith
    have hmul : (4 * c + 2) * s ≤ s ^ 2 := by
      have := mul_le_mul_of_nonneg_right hC hs0
      nlinarith [this]
    nlinarith [h4, hmul, hs2]
  calc t = s ^ 4 := hs4.symm
    _ < (4 * c + 3) ^ 4 := pow_lt_pow_left₀ hslt hs0 (by norm_num)

/-- The numeric core of `SmallExcSupport`: if `R + 1 ≤ C₀ log₂ (R+2) + 2 (R+2)^{1/4}` (with `C₀ ≥ 1`) then `R + 1 ≤ (4C₀+3)^4`.  Suggested route: put `t = R+2`, `s = t^{1/4}`; if `s ≥ 4C₀+3` then `t - 1 ≤ C₀·4·log₂ s + 2s ≤ (4C₀+2)s` (using `log₂ s ≤ s` for `s ≥ 1`, e.g. from `s < ⌊s⌋+1 ≤ 2^{⌊s⌋} ≤ 2^s`), so `s^4 ≤ (4C₀+2)s + 1 < (4C₀+3)s^3 ≤ s^4`, a contradiction; hence `s < 4C₀+3` and `R+1 < t = s^4 < (4C₀+3)^4`. -/
theorem smallExcNumeric (C₀ R : ℕ) (hC₀ : 1 ≤ C₀)
    (h : (R : ℝ) + 1 ≤ (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2) + 2 * ((R : ℝ) + 2) ^ ((1 : ℝ) / 4)) :
    R + 1 ≤ (4 * C₀ + 3) ^ 4 := by
  have hc : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have ht2 : (2 : ℝ) ≤ (R : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    linarith
  have key : (R : ℝ) + 2 < (4 * (C₀ : ℝ) + 3) ^ 4 :=
    four_mul_logb_core hc ht2 (by linarith [h])
  have key' : ((R + 2 : ℕ) : ℝ) < (((4 * C₀ + 3) ^ 4 : ℕ) : ℝ) := by
    have h1 : ((R + 2 : ℕ) : ℝ) = (R : ℝ) + 2 := by push_cast; ring
    have h2 : (((4 * C₀ + 3) ^ 4 : ℕ) : ℝ) = (4 * (C₀ : ℝ) + 3) ^ 4 := by push_cast; ring
    rw [h1, h2]; exact key
  have hfin : R + 2 ≤ (4 * C₀ + 3) ^ 4 := by exact_mod_cast (le_of_lt key')
  omega

end Work.KMTAreas.A7
