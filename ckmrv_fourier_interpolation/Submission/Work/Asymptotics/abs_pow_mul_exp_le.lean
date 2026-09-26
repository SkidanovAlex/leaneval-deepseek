import Mathlib
import Submission.Work.Asymptotics.Basic

namespace Work.Asymptotics

/-- The elementary real inequality `x e^{-x} ≤ e^{-1}` for all `x : ℝ`, the one-variable
maximum fact underlying the CKMRV bound `max_{r} |r|^c e^{-π r² t} = (c/(2πet))^{c/2}`.  It is
proved by taking logarithms (`Real.log_le_sub_one_of_pos`) in the case `x > 0`; for `x ≤ 0` the
left-hand side is nonpositive. -/
lemma mul_exp_neg_le (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  by_cases hx : x ≤ 0
  · have hle : x * Real.exp (-x) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg hx
      exact Real.exp_nonneg _
    have h1 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    linarith
  · have hx' : 0 < x := lt_of_not_ge hx
    have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx'
    have hxeq : x = Real.exp (Real.log x) := (Real.exp_log hx').symm
    rw [hxeq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

/-- The paper's elementary bound `max_{r ∈ ℝ} |r^c e^{-π r²t}| = (c/(2πet))^{c/2}` (CKMRV
equation `eq:moderateGaussian`), used to control the `r`-derivatives of the contour integral
uniformly in `r`. -/
theorem abs_pow_mul_exp_le (c : ℕ) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    |r| ^ c * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ ((c : ℝ) / (2 * Real.pi * Real.exp 1 * t)) ^ ((c : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp only [Nat.cast_zero, pow_zero, one_mul]
    rw [zero_div, show ((0 : ℝ) / 2) = 0 by norm_num, Real.rpow_zero]
    rw [Real.exp_le_one_iff]
    have hnn : 0 ≤ Real.pi * r ^ 2 * t :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht.le
    linarith
  · have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    -- Substitute `x = B r²` with `B = 2πt/c` in `x e^{-x} ≤ e^{-1}`.
    set B : ℝ := 2 * Real.pi * t / (c : ℝ) with hBdef
    have hBpos : 0 < B := by
      rw [hBdef]
      exact div_pos (by positivity) hcR
    have hx : (B * r ^ 2) * Real.exp (-(B * r ^ 2)) ≤ Real.exp (-1) :=
      mul_exp_neg_le (B * r ^ 2)
    have hstep1 : B * (r ^ 2 * Real.exp (-(B * r ^ 2))) ≤ Real.exp (-1) := by
      rw [← mul_assoc]; exact hx
    -- Divide by `B`: `r² e^{-B r²} ≤ e^{-1}/B = 1/(B e)`.
    have hstep2 : r ^ 2 * Real.exp (-(B * r ^ 2)) ≤ Real.exp (-1) / B := by
      rw [le_div_iff₀ hBpos]
      calc r ^ 2 * Real.exp (-(B * r ^ 2)) * B
          = B * (r ^ 2 * Real.exp (-(B * r ^ 2))) := by ring
        _ ≤ Real.exp (-1) := hstep1
    have hBe : Real.exp (-1) / B = 1 / (B * Real.exp 1) := by
      rw [Real.exp_neg]; field_simp
    have hstep4 : r ^ 2 * Real.exp (-(B * r ^ 2)) ≤ 1 / (B * Real.exp 1) := by
      rw [← hBe]; exact hstep2
    -- Raise both sides to the power `c/2`.
    have hbase : 0 ≤ r ^ 2 * Real.exp (-(B * r ^ 2)) := by positivity
    have hpow : (r ^ 2 * Real.exp (-(B * r ^ 2))) ^ ((c : ℝ) / 2)
        ≤ (1 / (B * Real.exp 1)) ^ ((c : ℝ) / 2) :=
      Real.rpow_le_rpow hbase hstep4 (by positivity)
    have hrpow : (r ^ 2) ^ ((c : ℝ) / 2) = |r| ^ c := by
      rw [show (r ^ 2 : ℝ) = |r| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs]]
      rw [← Real.rpow_mul (abs_nonneg r) (2 : ℝ) ((c : ℝ) / 2)]
      rw [show (2 : ℝ) * ((c : ℝ) / 2) = (c : ℝ) by ring]
      rw [Real.rpow_natCast]
    have hexppart : (Real.exp (-(B * r ^ 2))) ^ ((c : ℝ) / 2)
        = Real.exp (-(Real.pi * r ^ 2 * t)) := by
      rw [← Real.exp_mul]
      congr 1
      rw [hBdef]
      field_simp
    have eq1 : (r ^ 2 * Real.exp (-(B * r ^ 2))) ^ ((c : ℝ) / 2)
        = |r| ^ c * Real.exp (-(Real.pi * r ^ 2 * t)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), hrpow, hexppart]
    have eq2 : (1 / (B * Real.exp 1)) ^ ((c : ℝ) / 2)
        = ((c : ℝ) / (2 * Real.pi * Real.exp 1 * t)) ^ ((c : ℝ) / 2) := by
      congr 1
      rw [hBdef]
      field_simp
    rw [← eq1, ← eq2]
    exact hpow

end Work.Asymptotics
