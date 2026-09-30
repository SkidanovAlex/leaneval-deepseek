import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Arithmetic core: the reciprocal of `2 * r * s` written with the casts of `r` and `s`. -/
private lemma cast_mul_inv_eq_one (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ((2 * r * s : ℕ) : ℝ) * ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) = 1 := by
  have h2 : ((2 * r * s : ℕ) : ℝ) = 2 * (r : ℝ) * (s : ℝ) := by push_cast; ring
  rw [h2]
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hs0 : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  field_simp

/-- Extracting a root of an inequality between nonnegative reals: if `x ^ n ≤ A ^ n * P` then
`x ≤ A * P ^ (1 / n)`, for `n = 2 * r * s`. -/
theorem root_le (x A P : ℝ) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hx : 0 ≤ x) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (h : x ^ (2 * r * s) ≤ A ^ (2 * r * s) * P) :
    x ≤ A * P ^ ((1 : ℝ) / (2 * (r : ℝ) * (s : ℝ))) := by
  set c : ℝ := (1 : ℝ) / (2 * (r : ℝ) * (s : ℝ)) with hc_def
  have hc : (0 : ℝ) ≤ c := by positivity
  -- raise the hypothesis to the power `1 / (2 * r * s)`
  have hkey : (x ^ (2 * r * s)) ^ c ≤ (A ^ (2 * r * s) * P) ^ c :=
    Real.rpow_le_rpow (by positivity) h hc
  -- left hand side collapses to `x`
  have hL : (x ^ (2 * r * s)) ^ c = x := by
    rw [← Real.rpow_natCast_mul hx (2 * r * s) c,
      cast_mul_inv_eq_one r s hr hs, Real.rpow_one]
  -- right hand side collapses to `A * P ^ c`
  have hR : (A ^ (2 * r * s) * P) ^ c = A * P ^ c := by
    rw [Real.mul_rpow (by positivity) hP]
    congr 1
    rw [← Real.rpow_natCast_mul hA (2 * r * s) c,
      cast_mul_inv_eq_one r s hr hs, Real.rpow_one]
  rw [hL, hR] at hkey
  exact hkey

end Work.BMF
