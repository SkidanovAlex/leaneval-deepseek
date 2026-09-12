import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_lower_bound

namespace Commons.Analysis.Real

/-- `√(x^k) = (√x)^k` for `x ≥ 0`. -/
lemma sqrt_pow_of_nonneg (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  induction k with
  | zero => simp
  | succ m ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx m) x, ih, pow_succ]

/-- `2√x ≤ x + 1` for `x ≥ 0`, by AM-GM. -/
lemma two_mul_sqrt_le (x : ℝ) (hx : 0 ≤ x) : 2 * Real.sqrt x ≤ x + 1 := by
  nlinarith [sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt hx]

/-- `√x ≤ x` for `x ≥ 1`. -/
lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have h0 : 0 ≤ x := le_trans zero_le_one hx
  rw [Real.sqrt_le_left h0]
  nlinarith

/-- The square-root part of the coefficient bound: with `b = n(r+1)`, the quantity
`2^r · √b · ((H+1)^d + 1) · √((nr)^r)` is at most `2 · b^(r+1) · (H+1)^d`. -/
lemma sqrt_factor_bound (n r d : ℕ) (H : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hH : 0 ≤ H) :
    2^r * (Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1)) * Real.sqrt (((n:ℝ)*(r:ℝ))^r)
      ≤ 2 * ((n:ℝ)*((r:ℝ)+1))^(r+1) * (H+1)^d := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hH1 : (1:ℝ) ≤ H + 1 := by linarith
  set x : ℝ := (n:ℝ) * (r:ℝ) with hx
  set b : ℝ := (n:ℝ) * ((r:ℝ)+1) with hb
  have hx1 : (1:ℝ) ≤ x := by
    rw [hx]
    have h := mul_le_mul hn1 hr1 (by norm_num : (0:ℝ) ≤ (1:ℝ)) (by linarith : (0:ℝ) ≤ (n:ℝ))
    simpa using h
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hb1 : (1:ℝ) ≤ b := by
    rw [hb]
    have h := mul_le_mul hn1 (by linarith : (1:ℝ) ≤ (r:ℝ)+1) (by norm_num : (0:ℝ) ≤ (1:ℝ))
      (by linarith : (0:ℝ) ≤ (n:ℝ))
    simpa using h
  have hb0 : (0:ℝ) ≤ b := by linarith
  have hpow1 : 2^r * Real.sqrt (x^r) ≤ b^r := by
    rw [sqrt_pow_of_nonneg x hx0 r, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have h2sx : 2 * Real.sqrt x ≤ x + 1 := two_mul_sqrt_le x hx0
    have hx1b : x + 1 ≤ b := by rw [hx, hb]; nlinarith [hn1]
    linarith
  have hsqrtb : Real.sqrt b ≤ b := sqrt_le_self b hb1
  have hS : (H+1)^d + 1 ≤ 2 * (H+1)^d := by
    have h1 : (1:ℝ) ≤ (H+1)^d := one_le_pow₀ hH1
    linarith
  have hstep : Real.sqrt b * ((H+1)^d + 1) ≤ b * (2 * (H+1)^d) :=
    mul_le_mul hsqrtb hS (by positivity) hb0
  have hCm : 2^r * (Real.sqrt b * ((H+1)^d + 1)) * Real.sqrt (x^r)
      = (2^r * Real.sqrt (x^r)) * (Real.sqrt b * ((H+1)^d + 1)) := by ring
  rw [hCm]
  calc (2^r * Real.sqrt (x^r)) * (Real.sqrt b * ((H+1)^d + 1))
      ≤ b^r * (b * (2 * (H+1)^d)) := mul_le_mul hpow1 hstep (by positivity) (by positivity)
    _ = 2 * b^(r+1) * (H+1)^d := by rw [pow_succ]; ring

/-- The power part of the coefficient bound: for `b ≥ 2`, `d ≥ 1`, `H ≥ 0`,
`2 · b^(r+10) · (H+1)^(r+d+10) ≤ (b · d · (H+1))^(r+d+10)`. -/
lemma pow_mul_bound (b : ℝ) (d : ℕ) (H : ℝ) (k r : ℕ) (hk : k = r + d + 10)
    (hb : 2 ≤ b) (hd : 1 ≤ d) (hH : 0 ≤ H) :
    2 * (b^(r+10) * (H+1)^k) ≤ (b * (d:ℝ) * (H+1))^k := by
  subst hk
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hbd : (2:ℝ) ≤ b^d := by
    have h : b^1 ≤ b^d := pow_le_pow_right₀ hb1 (by omega)
    rw [pow_one] at h
    linarith
  have hdk : (1:ℝ) ≤ (d:ℝ)^(r+d+10) := one_le_pow₀ hd1
  have hkey : (2:ℝ) ≤ b^d * (d:ℝ)^(r+d+10) := by
    have h := mul_le_mul hbd hdk (by norm_num : (0:ℝ) ≤ (1:ℝ)) (by positivity : (0:ℝ) ≤ b^d)
    simpa using h
  have hH0 : 0 ≤ (H+1)^(r+d+10) := by
    have : 0 ≤ H + 1 := by linarith
    positivity
  have hmul : 2 * b^(r+10) ≤ b^(r+d+10) * (d:ℝ)^(r+d+10) := by
    have hbpow0 : 0 ≤ b^(r+10) := by positivity
    have h1 : b^(r+d+10) = b^(r+10) * b^d := by
      rw [show r+d+10 = (r+10)+d by omega, pow_add]
    rw [h1]
    calc 2 * b^(r+10) ≤ (b^d * (d:ℝ)^(r+d+10)) * b^(r+10) :=
            mul_le_mul_of_nonneg_right hkey hbpow0
      _ = b^(r+10) * b^d * (d:ℝ)^(r+d+10) := by ring
  calc 2 * (b^(r+10) * (H+1)^(r+d+10))
      = (2 * b^(r+10)) * (H+1)^(r+d+10) := by ring
    _ ≤ (b^(r+d+10) * (d:ℝ)^(r+d+10)) * (H+1)^(r+d+10) :=
          mul_le_mul_of_nonneg_right hmul hH0
    _ = (b * (d:ℝ) * (H+1))^(r+d+10) := by rw [mul_pow, mul_pow]

/-- Final arithmetic bound: the Minkowski root bound plus `1` is dominated by
`(n(r+1)d(H+1))^(r+d+10)`. -/
lemma final_bound (n r d : ℕ) (H : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hd : 1 ≤ d) (hH : 0 ≤ H) :
    2^r * (Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1)) * Real.sqrt (((n:ℝ)*(r:ℝ))^r) + 1
      ≤ ((n:ℝ)*((r:ℝ)+1)*(d:ℝ)*(H+1))^(r+d+10) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hH1 : (1:ℝ) ≤ H + 1 := by linarith
  have hb2 : (2:ℝ) ≤ (n:ℝ)*((r:ℝ)+1) := by
    have h := mul_le_mul hn1 (by linarith : (2:ℝ) ≤ (r:ℝ)+1) (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by linarith : (0:ℝ) ≤ (n:ℝ))
    simpa using h
  have hb1 : (1:ℝ) ≤ (n:ℝ)*((r:ℝ)+1) := by linarith
  have hP1 : (1:ℝ) ≤ ((n:ℝ)*((r:ℝ)+1))^(r+10) * (H+1)^(r+d+10) := by
    have ha : (1:ℝ) ≤ ((n:ℝ)*((r:ℝ)+1))^(r+10) := one_le_pow₀ hb1
    have hb : (1:ℝ) ≤ (H+1)^(r+d+10) := one_le_pow₀ hH1
    have h := mul_le_mul ha hb (by norm_num : (0:ℝ) ≤ (1:ℝ))
      (by positivity : (0:ℝ) ≤ ((n:ℝ)*((r:ℝ)+1))^(r+10))
    simpa using h
  have hC4 : 2 * (((n:ℝ)*((r:ℝ)+1))^(r+10) * (H+1)^(r+d+10))
      ≤ ((n:ℝ)*((r:ℝ)+1)*(d:ℝ)*(H+1))^(r+d+10) :=
    pow_mul_bound ((n:ℝ)*((r:ℝ)+1)) d H (r+d+10) r rfl hb2 hd hH
  have h2b : 2 * ((n:ℝ)*((r:ℝ)+1))^(r+1) ≤ ((n:ℝ)*((r:ℝ)+1))^(r+10) := by
    have hb9 : (2:ℝ) ≤ ((n:ℝ)*((r:ℝ)+1))^9 := by
      have h : ((n:ℝ)*((r:ℝ)+1))^1 ≤ ((n:ℝ)*((r:ℝ)+1))^9 :=
        pow_le_pow_right₀ hb1 (by norm_num)
      rw [pow_one] at h
      linarith
    calc 2 * ((n:ℝ)*((r:ℝ)+1))^(r+1)
        ≤ ((n:ℝ)*((r:ℝ)+1))^9 * ((n:ℝ)*((r:ℝ)+1))^(r+1) :=
          mul_le_mul_of_nonneg_right hb9 (by positivity)
      _ = ((n:ℝ)*((r:ℝ)+1))^(r+10) := by rw [← pow_add]; congr 1; omega
  have hHd : (H+1)^d ≤ (H+1)^(r+d+10) := pow_le_pow_right₀ hH1 (by omega)
  have h1 : 2 * ((n:ℝ)*((r:ℝ)+1))^(r+1) * (H+1)^d
      ≤ ((n:ℝ)*((r:ℝ)+1))^(r+10) * (H+1)^(r+d+10) :=
    mul_le_mul h2b hHd (by positivity) (by positivity)
  have hC : 2^r * (Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1)) * Real.sqrt (((n:ℝ)*(r:ℝ))^r)
      ≤ 2 * ((n:ℝ)*((r:ℝ)+1))^(r+1) * (H+1)^d := sqrt_factor_bound n r d H hn hr hH
  have hC3 : 2^r * (Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1)) * Real.sqrt (((n:ℝ)*(r:ℝ))^r) + 1
      ≤ 2 * (((n:ℝ)*((r:ℝ)+1))^(r+10) * (H+1)^(r+d+10)) := by
    linarith [hC, h1, hP1]
  exact le_trans hC3 hC4

/-- Minkowski-type root bound: from the volume lower bound `v ≥ (2/√(nr))^(nr)` one gets
`(4^(nr) A^n / v)^(1/n) ≤ C`, where `A = √(n(r+1)) ((H+1)^d+1)` and
`C = 2^r A √((nr)^r)`. -/
lemma root_bound (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (H : ℝ) (hH : 0 ≤ H) (d : ℕ) {v : ℝ}
    (hv : 0 < v) (hvol : (2 / Real.sqrt ((n : ℝ) * (r : ℝ))) ^ (n * r) ≤ v) :
    (4 ^ (n * r) * (Real.sqrt ((n : ℝ) * ((r : ℝ) + 1)) * ((H + 1) ^ d + 1)) ^ n / v)
        ^ ((1 : ℝ) / (n : ℝ))
      ≤ 2^r * (Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1)) * Real.sqrt (((n:ℝ)*(r:ℝ))^r) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hnne : n ≠ 0 := by omega
  set x : ℝ := (n:ℝ) * (r:ℝ) with hx
  have hx1 : (1:ℝ) ≤ x := by
    rw [hx]
    have h := mul_le_mul hn1 hr1 (by norm_num : (0:ℝ) ≤ (1:ℝ)) (by linarith : (0:ℝ) ≤ (n:ℝ))
    simpa using h
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsxne : Real.sqrt x ≠ 0 := ne_of_gt hsxpos
  have hvolx : (2 / Real.sqrt x)^(n*r) ≤ v := by simpa [hx] using hvol
  have hA := mul_le_mul_of_nonneg_right hvolx (by positivity : (0:ℝ) ≤ (Real.sqrt x)^(n*r))
  have hA2 : (2 / Real.sqrt x)^(n*r) * (Real.sqrt x)^(n*r) = 2^(n*r) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h2nr : 2^(n*r) ≤ v * (Real.sqrt x)^(n*r) := by
    rw [← hA2]
    exact hA
  have h4 : 4^(n*r) ≤ v * 2^(n*r) * (Real.sqrt x)^(n*r) := by
    have h := mul_le_mul_of_nonneg_right h2nr (by positivity : (0:ℝ) ≤ (2:ℝ)^(n*r))
    calc (4:ℝ)^(n*r) = 2^(n*r) * 2^(n*r) := by rw [← mul_pow]; norm_num
      _ ≤ (v * (Real.sqrt x)^(n*r)) * 2^(n*r) := h
      _ = v * 2^(n*r) * (Real.sqrt x)^(n*r) := by ring
  have hH1 : (1:ℝ) ≤ H + 1 := by linarith
  have hSpos : 0 < (H+1)^d + 1 := by
    have h1 : (1:ℝ) ≤ (H+1)^d := one_le_pow₀ hH1
    linarith
  have hsq : 0 < Real.sqrt ((n:ℝ)*((r:ℝ)+1)) :=
    Real.sqrt_pos.mpr (mul_pos hn0 (by linarith : (0:ℝ) < (r:ℝ)+1))
  have hApos : 0 < Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1) := mul_pos hsq hSpos
  set A : ℝ := Real.sqrt ((n:ℝ)*((r:ℝ)+1)) * ((H+1)^d + 1) with hAdef
  set C : ℝ := 2^r * A * Real.sqrt (x^r) with hCdef
  have hCn : C^n = 2^(n*r) * A^n * (Real.sqrt x)^(n*r) := by
    rw [hCdef, mul_pow, mul_pow]
    rw [sqrt_pow_of_nonneg x hx0 r, ← pow_mul, ← pow_mul]
    rw [mul_comm r n]
  have hBC : 4^(n*r) * A^n / v ≤ C^n := by
    rw [hCn, div_le_iff₀ hv]
    have hA0 : 0 ≤ A := le_of_lt hApos
    have hAn : 0 ≤ A^n := pow_nonneg hA0 n
    calc 4^(n*r) * A^n ≤ (v * 2^(n*r) * (Real.sqrt x)^(n*r)) * A^n :=
          mul_le_mul_of_nonneg_right h4 hAn
      _ = (2^(n*r) * A^n * (Real.sqrt x)^(n*r)) * v := by ring
  have hB0 : 0 ≤ 4^(n*r) * A^n / v := by positivity
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hroot1 : (4^(n*r) * A^n / v)^((1:ℝ)/(n:ℝ)) ≤ (C^n)^((1:ℝ)/(n:ℝ)) :=
    Real.rpow_le_rpow hB0 hBC (by positivity)
  have hroot2 : (C^n)^((1:ℝ)/(n:ℝ)) = C := by
    rw [one_div, Real.pow_rpow_inv_natCast hC0 hnne]
  exact le_trans hroot1 (le_of_eq hroot2)

-- Arithmetic for the coefficient bound of `small_relations_of_wellPoised`.
-- With A := sqrt(n(r+1)) * ((H+1)^d + 1) and v >= (2/sqrt(n r))^(n r) (a lower bound for the
-- volume of the unit ball of R^(n r)), the Minkowski-type bound
--   (4^(n r) * A^n / v)^(1/n) + 1
-- is at most (n (r+1) d (H+1))^(r+d+10).
-- Route: from v >= 2^(n r)/(sqrt(n r))^(n r) and (sqrt((n r)^r))^n = (sqrt(n r))^(n r) one gets
-- 4^(n r) <= v * 2^(n r) * (sqrt((n r)^r))^n, hence (4^(n r) * A^n / v) <= (2^r * A * sqrt((n r)^r))^n,
-- and taking the (1/n)-th root gives the bound 2^r * A * sqrt((n r)^r) + 1; finally
-- 2^r * sqrt(n(r+1)) * ((H+1)^d + 1) * sqrt((n r)^r) <= (n(r+1))^(r+10) * (H+1)^(r+d+10)
-- <= (n (r+1) d (H+1))^(r+d+10) using n(r+1) >= 2 and 2^(r+1) <= (n(r+1))^(r+10).
lemma coeff_bound_arith (n r d : ℕ) (H : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hd : 1 ≤ d) (hH : 0 ≤ H)
    {v : ℝ} (hv : 0 < v)
    (hvol : (2 / Real.sqrt ((n : ℝ) * (r : ℝ))) ^ (n * r) ≤ v) :
    (4 ^ (n * r) * (Real.sqrt ((n : ℝ) * ((r : ℝ) + 1)) * ((H + 1) ^ d + 1)) ^ n / v)
        ^ ((1 : ℝ) / (n : ℝ)) + 1
      ≤ ((n : ℝ) * ((r : ℝ) + 1) * (d : ℝ) * (H + 1)) ^ (r + d + 10) := by
  exact le_trans (add_le_add (root_bound n r hn hr H hH d hv hvol) (le_refl 1))
    (final_bound n r d H hn hr hd hH)

end Commons.Analysis.Real