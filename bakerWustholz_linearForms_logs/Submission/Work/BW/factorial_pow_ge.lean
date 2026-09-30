import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A factorial-vs-power estimate for the Baker--Wüstholz development

We prove, for every natural number `r ≥ 2`,

  `105.93 * (11.75 * r + 1)^r ≤ 32^(r+1) * r!`.

The constants are chosen so that the ratio
`f(r) = 32 * r! / (105.93 * ((11.75 r + 1)/32)^r)`
is increasing for `r ≥ 2`, with `f(2) ≥ 1`.  Concretely, the induction step uses

  `(11.75(r+1)+1)^(r+1) ≤ 32 (r+1) (11.75 r + 1)^r`,

which reduces (after writing `s = 11.75 r + 1`) to

  `(s + 11.75) * (1 + 11.75/s)^r ≤ 32 (r + 1)`.

Since `r * log(1 + 11.75/s) ≤ r * 11.75 / s = 1 - 1/s` and `e^{-1/s} ≤ 1/(1+1/s)`,
the left side is at most `(s + 11.75) * e * s/(s+1) ≤ (s + 11.75) * 2.72 * s/(s+1)`,
and `11.75 * 2.72 * s * (s + 11.75) ≤ 32 (s + 10.75)(s+1)` is elementary.
-/

namespace Work.BW

/-- For `t ≥ 0`, `exp (-t) ≤ 1/(1+t)`. -/
lemma factorial_pow_ge_exp_neg_le_one_div (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 / (1 + t) := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hpos : 0 < 1 + t := by linarith
  rw [Real.exp_neg]
  simpa [one_div] using one_div_le_one_div_of_le hpos h1

/-- Key exponential estimate: for `s > 0` with `11.75 * r = s - 1`,
`(1 + 11.75/s)^r ≤ e * s/(s+1)`. -/
lemma factorial_pow_ge_key_ratio (r : ℕ) (s : ℝ) (hs : 0 < s)
    (hrel : 11.75 * (r : ℝ) = s - 1) :
    (1 + 11.75 / s) ^ r ≤ Real.exp 1 * (s / (s + 1)) := by
  have hx : 0 < 1 + 11.75 / s := by positivity
  have hlog : Real.log (1 + 11.75 / s) ≤ 11.75 / s := by
    have h := Real.log_le_sub_one_of_pos hx
    have hh : (1 + 11.75 / s) - 1 = 11.75 / s := by ring
    linarith [h, hh]
  have hstep1 : (1 + 11.75 / s) ^ r ≤ Real.exp (11.75 * (r : ℝ) / s) := by
    rw [← Real.exp_log hx, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg r)
    simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hm
  have hexpand : 11.75 * (r : ℝ) / s = 1 + (-(1 / s)) := by
    field_simp
    linarith [hrel]
  have hstep2 : Real.exp (11.75 * (r : ℝ) / s) ≤ Real.exp 1 * (s / (s + 1)) := by
    rw [hexpand, Real.exp_add]
    have hb : Real.exp (-(1 / s)) ≤ 1 / (1 + 1 / s) :=
      factorial_pow_ge_exp_neg_le_one_div (1 / s) (by positivity)
    have hfrac : (1 : ℝ) / (1 + 1 / s) = s / (s + 1) := by field_simp
    calc Real.exp 1 * Real.exp (-(1 / s))
        ≤ Real.exp 1 * (1 / (1 + 1 / s)) := by
            apply mul_le_mul_of_nonneg_left hb (le_of_lt (Real.exp_pos 1))
      _ = Real.exp 1 * (s / (s + 1)) := by rw [hfrac]
  linarith [hstep1, hstep2]

/-- An elementary numerical inequality with the rational upper bound `e ≤ 2.72`. -/
lemma factorial_pow_ge_numeric (r : ℕ) :
    2.72 * (11.75 * (r : ℝ) + 1) * (11.75 * (r : ℝ) + 1 + 11.75)
      ≤ 32 * ((r : ℝ) + 1) * (11.75 * (r : ℝ) + 1 + 1) := by
  nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ))]

/-- The reduced induction step: `(s+11.75) * (1+11.75/s)^r ≤ 32(r+1)` for `s = 11.75 r + 1`. -/
lemma factorial_pow_ge_ratio_step (r : ℕ) (hr : 2 ≤ r) :
    (11.75 * ((r : ℝ) + 1) + 1) * (1 + 11.75 / (11.75 * (r : ℝ) + 1)) ^ r
      ≤ 32 * ((r : ℝ) + 1) := by
  set s : ℝ := 11.75 * (r : ℝ) + 1 with hsdef
  have hs_pos : 0 < s := by rw [hsdef]; positivity
  have hrel : 11.75 * (r : ℝ) = s - 1 := by rw [hsdef]; ring
  have hkey := factorial_pow_ge_key_ratio r s hs_pos hrel
  have hexp_le : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have hs1 : 0 < s + 1 := by linarith
  have hfrac : 0 ≤ s / (s + 1) := by positivity
  have heq : 11.75 * ((r : ℝ) + 1) + 1 = s + 11.75 := by rw [hsdef]; ring
  rw [heq]
  have hbound : (1 + 11.75 / s) ^ r ≤ (2.72 * s) / (s + 1) := by
    calc (1 + 11.75 / s) ^ r ≤ Real.exp 1 * (s / (s + 1)) := hkey
      _ ≤ 2.72 * (s / (s + 1)) := mul_le_mul_of_nonneg_right hexp_le hfrac
      _ = (2.72 * s) / (s + 1) := by rw [mul_div_assoc]
  have hA : (s + 11.75) * (1 + 11.75 / s) ^ r ≤ (s + 11.75) * ((2.72 * s) / (s + 1)) :=
    mul_le_mul_of_nonneg_left hbound (by linarith)
  have hnum' : 2.72 * s * (s + 11.75) ≤ 32 * ((r : ℝ) + 1) * (s + 1) := by
    rw [hsdef]; exact factorial_pow_ge_numeric r
  have hB : (s + 11.75) * ((2.72 * s) / (s + 1)) ≤ 32 * ((r : ℝ) + 1) := by
    rw [← mul_div_assoc, div_le_iff₀ hs1]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum'
  linarith [hA, hB]

/-- The induction step in the form used below:
`(11.75(r+1)+1)^(r+1) ≤ 32 (r+1) (11.75 r + 1)^r` for `r ≥ 2`. -/
lemma factorial_pow_ge_ratio_ineq (r : ℕ) (hr : 2 ≤ r) :
    (11.75 * ((r : ℝ) + 1) + 1) ^ (r + 1)
      ≤ 32 * ((r : ℝ) + 1) * (11.75 * (r : ℝ) + 1) ^ r := by
  set s : ℝ := 11.75 * (r : ℝ) + 1 with hsdef
  have hs_pos : 0 < s := by rw [hsdef]; positivity
  have heq : 11.75 * ((r : ℝ) + 1) + 1 = s + 11.75 := by rw [hsdef]; ring
  have hstep := factorial_pow_ge_ratio_step r hr
  rw [← hsdef] at hstep
  rw [heq] at hstep
  have hsr : (s + 11.75) * (1 + 11.75 / s) ^ r * s ^ r ≤ 32 * ((r : ℝ) + 1) * s ^ r :=
    mul_le_mul_of_nonneg_right hstep (by positivity)
  have hL : (s + 11.75) * (1 + 11.75 / s) ^ r * s ^ r = (s + 11.75) ^ (r + 1) := by
    rw [mul_assoc, ← mul_pow]
    have hspl : (1 + 11.75 / s) * s = s + 11.75 := by field_simp
    rw [hspl, pow_succ']
  rw [heq, ← hL]
  exact hsr

theorem factorial_pow_ge (r : ℕ) (hr : 2 ≤ r) :
    (105.93 : ℝ) * (11.75 * (r : ℝ) + 1) ^ r ≤ (32 : ℝ) ^ (r + 1) * (r.factorial : ℝ) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hratio := factorial_pow_ge_ratio_ineq n hn
      calc (105.93 : ℝ) * (11.75 * ((n + 1 : ℕ) : ℝ) + 1) ^ (n + 1)
          = (105.93 : ℝ) * (11.75 * ((n : ℝ) + 1) + 1) ^ (n + 1) := by push_cast; ring
          _ ≤ (105.93 : ℝ) * (32 * ((n : ℝ) + 1) * (11.75 * (n : ℝ) + 1) ^ n) := by
                apply mul_le_mul_of_nonneg_left hratio (by norm_num)
          _ = 32 * ((n : ℝ) + 1) * ((105.93 : ℝ) * (11.75 * (n : ℝ) + 1) ^ n) := by ring
          _ ≤ 32 * ((n : ℝ) + 1) * ((32 : ℝ) ^ (n + 1) * (n.factorial : ℝ)) := by
                apply mul_le_mul_of_nonneg_left ih (by positivity)
          _ = (32 : ℝ) ^ (n + 1 + 1) * ((n + 1).factorial : ℝ) := by
                rw [Nat.factorial_succ, pow_succ]; push_cast; ring

end Work.BW
