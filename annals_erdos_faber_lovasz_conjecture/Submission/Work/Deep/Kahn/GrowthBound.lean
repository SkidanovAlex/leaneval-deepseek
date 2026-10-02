/-
# Elementary growth bounds for the parameter estimates of the nibble iteration

The point of these lemmas is that every numerical condition `It.Cond` for the concrete
parameters `mkIt` reduces to "exponential dominates polynomial in `log`", i.e. to
`log x ≤ 2000 x^(1/2000)` and the monotonicity of `exp`.
-/
import Submission.Work.ConeSwitch.MathlibNoHG

set_option autoImplicit false

namespace Work.Deep.Kahn

/-- `log x ≤ 2000 * x ^ (1/2000)` for `x ≥ 0`. -/
lemma log_le_mul_rpow (x : ℝ) (hx : 0 ≤ x) :
    Real.log x ≤ 2000 * x ^ ((1 : ℝ) / 2000) := by
  have h := Real.log_le_rpow_div (x := x) hx (show (0:ℝ) < 1/2000 by norm_num)
  have h2 : x ^ ((1 : ℝ) / 2000) / (1 / 2000) = 2000 * x ^ ((1 : ℝ) / 2000) := by
    field_simp
  rwa [h2] at h

/-- `(log x) ^ n ≤ 2000 ^ n * x ^ (n/2000)` for `x ≥ 1`. -/
lemma log_pow_le (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    (Real.log x) ^ n ≤ (2000 : ℝ) ^ n * x ^ ((n : ℝ) / 2000) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h2 := log_le_mul_rpow x hx0
  have h3 : (x ^ ((1 : ℝ) / 2000)) ^ n = x ^ ((n : ℝ) / 2000) := by
    rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 2000)) n, ← Real.rpow_mul hx0,
      show (1 : ℝ) / 2000 * (n : ℝ) = (n : ℝ) / 2000 by ring]
  calc (Real.log x) ^ n ≤ (2000 * x ^ ((1 : ℝ) / 2000)) ^ n := pow_le_pow_left₀ h1 h2 n
    _ = (2000 : ℝ) ^ n * (x ^ ((1 : ℝ) / 2000)) ^ n := by rw [mul_pow]
    _ = (2000 : ℝ) ^ n * x ^ ((n : ℝ) / 2000) := by rw [h3]

/-- `x ^ a ≤ x ^ b` for `x ≥ 1` and `a ≤ b`. -/
lemma rpow_le_rpow_of_exp_le {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (hab : a ≤ b) :
    x ^ a ≤ x ^ b := by
  have _ := hx
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · exact (Real.rpow_le_rpow_left_iff h).mpr hab

/-- `x ^ (1/2) ≤ x` for `x ≥ 1`. -/
lemma rpow_half_le_self {x : ℝ} (hx : 1 ≤ x) : x ^ ((1 : ℝ) / 2) ≤ x := by
  have h : x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exp_le hx (by norm_num)
  rwa [Real.rpow_one] at h

/-- `log x ≤ x` for `x ≥ 1`. -/
lemma log_le_self {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x := by
  have h := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < x)
  linarith

/-- `log (1/x) ≤ 1/x` for `0 < x ≤ 1`. -/
lemma log_inv_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : Real.log x⁻¹ ≤ x⁻¹ := by
  have h : (1:ℝ) ≤ x⁻¹ := by rw [one_le_inv₀ hx0]; exact hx1
  exact log_le_self h

/-- `x ≤ exp x` for `x ≥ 0`. -/
lemma self_le_exp {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  linarith

/-- `x ≤ exp (2000 * x ^ (1/2000))` for `x ≥ 1`. -/
lemma self_le_exp_mul_rpow {x : ℝ} (hx : 1 ≤ x) :
    x ≤ Real.exp (2000 * x ^ ((1 : ℝ) / 2000)) :=
  (Real.log_le_iff_le_exp (by linarith : (0:ℝ) < x)).mp (log_le_mul_rpow x (by linarith))

end Work.Deep.Kahn
