import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BW.num_xi` (BW §19–20 decimals for `ξ = 1 - 0.536/r`)

BW's reference: A. Baker, G. Wüstholz, *Logarithmic forms and group varieties*, J. reine
angew. Math. 442 (1993), 19–62, §19–20 (pp. 54–59).

The five facts recorded in `num_xi` bound `ξ = 1 - 0.536/r` (`pxi r`) and `b = 2ξ^r`.
All are pure real arithmetic. The two genuinely analytic ingredients are

* `num_xi_aux_step`, the compound-interest monotonicity `(1 - a/n)^n ≤ (1 - a/(n+1))^{n+1}`
  (`0 < a ≤ 1`, `n ≥ 2`), proved from Bernoulli's inequality — it shows that
  `n ↦ (1 - 0.536/n)^n` is increasing, so `ξ^r ≥ 0.732² = 0.535824 ≥ 0.535` (statements
  `0.535 ≤ ξ^r`, `2ξ^r ≥ 1.07` and, via inversion, `ξ^{-r} ≤ 1.87`);
* the one-sided `log(1-t)` bounds `-t/(1-t) ≤ log(1-t) ≤ -t` (`t < 1`) together with the
  third-order Taylor bound `e^x ≥ 1 + x + x²/2`, which give `ξ^{r-1} ≤ 0.732` and
  `ξ^j ≥ e^{-0.536}` for `j ≤ r-1`.
-/

namespace Work.BW

/-- **Step of the compound-interest monotonicity.** For `0 < a ≤ 1` and `n ≥ 2`,
`(1 - a/n)^n ≤ (1 - a/(n+1))^{n+1}`. Proved from Bernoulli's inequality: write `X = 1 - a/n`,
`Y = X + d` with `d = a/(n(n+1))`, so that `X + (n+1)d = 1`; then
`Y^{n+1} = X^n (1 + d/X)^n (X+d) ≥ X^n (1 + n d/X)(X+d) = X^n (X + (n+1)d) = X^n`. -/
theorem num_xi_aux_step {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    (1 - a / (n:ℝ)) ^ n ≤ (1 - a / ((n:ℝ)+1)) ^ (n+1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have han_lt : a / (n:ℝ) < 1 := by rw [div_lt_one hn0]; linarith
  set X := 1 - a/(n:ℝ) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; linarith
  set d := a/((n:ℝ)*((n:ℝ)+1)) with hddef
  have hdpos : 0 < d := by rw [hddef]; exact div_pos ha0 (by positivity)
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have hYeq : 1 - a/((n:ℝ)+1) = X + d := by rw [hXdef, hddef]; field_simp; ring
  have hXd1 : X + d + (n:ℝ)*d = 1 := by rw [hXdef, hddef]; field_simp; ring
  have hBern : (1 + (n:ℝ) * (d/X)) ≤ (1 + d/X)^n :=
    one_add_mul_le_pow (by have : 0 < d/X := div_pos hdpos hXpos; linarith) n
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have hpow : (X + d)^n = X^n * (1 + d/X)^n := by
    have hrw : X + d = X * (1 + d/X) := by
      rw [mul_add, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ d hXne]
    rw [hrw, mul_pow]
  have hA : X^n * (1 + (n:ℝ)*(d/X)) ≤ X^n * (1 + d/X)^n :=
    mul_le_mul_of_nonneg_left hBern (pow_nonneg (le_of_lt hXpos) n)
  have hratio1 : 1 ≤ (X+d)/X := by rw [le_div_iff₀ hXpos]; linarith
  have hprod : 1 ≤ (1 + (n:ℝ)*(d/X))*(X+d) := by
    have he : (1 + (n:ℝ)*(d/X))*(X+d) = (X+d) + (n:ℝ)*d*((X+d)/X) := by field_simp
    rw [he]
    have hextra : 0 ≤ (n:ℝ)*d*((X+d)/X - 1) :=
      mul_nonneg (mul_nonneg (by positivity) (le_of_lt hdpos)) (by linarith)
    nlinarith [hXd1]
  have hmain1 : X^n ≤ X^n * ((1 + (n:ℝ)*(d/X))*(X+d)) := by
    nth_rewrite 1 [show X^n = X^n * 1 by ring]
    exact mul_le_mul_of_nonneg_left hprod (pow_nonneg (le_of_lt hXpos) n)
  have hmain2 : X^n * ((1 + (n:ℝ)*(d/X))*(X+d)) ≤ (X+d)^(n+1) := by
    rw [pow_succ, hpow]
    have h2 : (X^n * (1 + (n:ℝ)*(d/X))) * (X+d) ≤ (X^n * (1 + d/X)^n) * (X+d) :=
      mul_le_mul_of_nonneg_right hA (by linarith [hdpos, hXpos])
    rwa [mul_assoc] at h2
  rw [hYeq]
  linarith [hmain1, hmain2]

/-- `log(1-t) ≥ -t/(1-t)` for `t < 1`, from `log x ≤ x - 1` at `x = (1-t)⁻¹`. -/
theorem num_xi_aux_log_lower {t : ℝ} (ht1 : t < 1) :
    -(t / (1 - t)) ≤ Real.log (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  have h2 : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp; ring
  linarith

/-- `log(1-t) ≤ -t` for `t < 1`, from `log x ≤ x - 1` at `x = 1-t`. -/
theorem num_xi_aux_log_upper {t : ℝ} (ht1 : t < 1) : Real.log (1 - t) ≤ -t := by
  have h1 : 0 < 1 - t := by linarith
  have h := Real.log_le_sub_one_of_pos h1
  linarith

/-- `exp(-2·0.536/3) ≤ 0.732`, via the third-order Taylor lower bound `e^x ≥ 1 + x + x²/2`. -/
theorem num_xi_aux_exp_bound : Real.exp (-(2*0.536/3)) ≤ 0.732 := by
  have hsum : (1.37:ℝ) ≤ Real.exp (2*0.536/3) := by
    have hx : (0:ℝ) ≤ 2*0.536/3 := by norm_num
    have h := Real.sum_le_exp_of_nonneg hx 3
    have hval : (∑ i ∈ Finset.range 3, (2*0.536/3)^i/(i.factorial:ℝ))
        = 1 + 2*0.536/3 + (2*0.536/3)^2/2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]; norm_num
    rw [hval] at h
    nlinarith [h]
  rw [Real.exp_neg]
  have hinv : (Real.exp (2*0.536/3))⁻¹ ≤ (1.37:ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hsum
  have hnum : (1.37:ℝ)⁻¹ ≤ 0.732 := by norm_num
  linarith

/-- BW §19–20 facts about `ξ = 1 − 0·536/r` and `b = 2ξ^r`: `ξ^{-r} ≤ 1·87` (p. 58), `ξ^r ≥ 0·535` (p. 57), `ξ^{r-1} ≤ 0·732` (p. 56), `ξ^j ≥ e^{-0·536}` for `j ≤ r−1` (p. 54–55), `b ≥ 1·07` (p. 59). -/
theorem num_xi {r : ℕ} (hr : 2 ≤ r) :
    pxi r ^ (-(r : ℤ)) ≤ 1.87 ∧ 0.535 ≤ pxi r ^ r ∧ pxi r ^ (r - 1) ≤ 0.732 ∧
      (∀ j, j ≤ r - 1 → Real.exp (-0.536) ≤ pxi r ^ j) ∧ 1.07 ≤ 2 * pxi r ^ r := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have h1n : 1 ≤ r := by omega
  have hxir : pxi r = 1 - (0.536:ℝ)/r := rfl
  have hxi_pos : 0 < pxi r := by
    rw [hxir]
    have : (0.536:ℝ)/r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hxi_le1 : pxi r ≤ 1 := by
    rw [hxir]
    have : (0:ℝ) ≤ (0.536:ℝ)/r := by positivity
    linarith
  have hxi_nonneg : 0 ≤ pxi r := le_of_lt hxi_pos
  -- (2)  `0.535 ≤ ξ^r`:  the sequence `n ↦ (1 - 0.536/n)^n` (n ≥ 2) is increasing,
  -- its minimum being attained at `n = 2`, where it equals `0.732² = 0.535824 ≥ 0.535`.
  have hmono : (1 - (0.536:ℝ)/2)^2 ≤ (1 - (0.536:ℝ)/r)^r := by
    refine Nat.le_induction (m := 2)
      (P := fun n _ => (1 - (0.536:ℝ)/2)^2 ≤ (1 - (0.536:ℝ)/n)^n)
      (le_refl _) (fun n hn ih => le_trans ih (by
        have h := num_xi_aux_step (a := 0.536) (by norm_num) (by norm_num) (n := n) hn
        simpa [Nat.cast_add, Nat.cast_one] using h)) r hr
  have h2 : 0.535 ≤ pxi r ^ r := by
    rw [hxir]
    have hbase : (0.535:ℝ) ≤ (1 - 0.536/2)^2 := by norm_num
    linarith
  -- (3)  `ξ^{r-1} ≤ 0.732`:  `r = 2` is an equality; for `r ≥ 3`,
  -- `ξ^{r-1} = e^{(r-1)log ξ} ≤ e^{-(r-1)0.536/r} ≤ e^{-2·0.536/3} ≤ 0.732`.
  have h3 : pxi r ^ (r - 1) ≤ 0.732 := by
    rcases eq_or_lt_of_le hr with h | h
    · subst h; norm_num [pxi]
    · have hr3 : (3:ℝ) ≤ r := by exact_mod_cast h
      have hlog : Real.log (pxi r) ≤ -(0.536/r) := by
        rw [hxir]
        exact num_xi_aux_log_upper (by rw [div_lt_one hr0]; linarith)
      have hcore : ((r-1:ℕ):ℝ) * Real.log (pxi r) ≤ -(2*0.536/3) := by
        have hfac : (0:ℝ) ≤ ((r-1:ℕ):ℝ) := by positivity
        have hfrac : (2:ℝ)/3 ≤ ((r-1:ℕ):ℝ)/r := by
          rw [Nat.cast_sub h1n, le_div_iff₀ hr0]; push_cast; linarith
        have hmul : 0.536*((2:ℝ)/3) ≤ 0.536*(((r-1:ℕ):ℝ)/r) :=
          mul_le_mul_of_nonneg_left hfrac (by norm_num)
        have step1 : ((r-1:ℕ):ℝ) * Real.log (pxi r) ≤ ((r-1:ℕ):ℝ) * (-(0.536/r)) :=
          mul_le_mul_of_nonneg_left hlog hfac
        calc ((r-1:ℕ):ℝ)*Real.log (pxi r) ≤ ((r-1:ℕ):ℝ)*(-(0.536/r)) := step1
          _ = -(0.536*(((r-1:ℕ):ℝ)/r)) := by ring
          _ ≤ -(2*0.536/3) := by nlinarith [hmul]
      have hexp : pxi r ^ (r-1) = Real.exp (((r-1:ℕ):ℝ)*Real.log (pxi r)) := by
        rw [← Real.exp_log (pow_pos hxi_pos (r-1)), Real.log_pow]
      rw [hexp]
      calc Real.exp (((r-1:ℕ):ℝ)*Real.log (pxi r)) ≤ Real.exp (-(2*0.536/3)) :=
            Real.exp_le_exp.mpr hcore
        _ ≤ 0.732 := num_xi_aux_exp_bound
  -- (4)  `ξ^j ≥ e^{-0.536}` for `j ≤ r-1`:  `ξ^j ≥ ξ^{r-1}` since `0 ≤ ξ ≤ 1`, and
  -- `(r-1)log ξ ≥ -(r-1)·0.536/r/(1-0.536/r) ≥ -0.536` by `log(1-t) ≥ -t/(1-t)`.
  have h4 : ∀ j, j ≤ r - 1 → Real.exp (-0.536) ≤ pxi r ^ j := by
    intro j hj
    have hbase : Real.exp (-0.536) ≤ pxi r ^ (r-1) := by
      have hexp : pxi r ^ (r-1) = Real.exp (((r-1:ℕ):ℝ)*Real.log (pxi r)) := by
        rw [← Real.exp_log (pow_pos hxi_pos (r-1)), Real.log_pow]
      rw [hexp]
      apply Real.exp_le_exp.mpr
      rw [hxir]
      have ht1 : (0.536:ℝ)/r < 1 := by rw [div_lt_one hr0]; linarith
      have hlog := num_xi_aux_log_lower ht1
      have hfac : (0:ℝ) ≤ ((r-1:ℕ):ℝ) := by positivity
      have hstep : ((r-1:ℕ):ℝ)*(-(((0.536:ℝ)/r)/(1 - (0.536:ℝ)/r))) ≤
          ((r-1:ℕ):ℝ)*Real.log (1 - (0.536:ℝ)/r) := mul_le_mul_of_nonneg_left hlog hfac
      have hkey : ((r-1:ℕ):ℝ)*(((0.536:ℝ)/r)/(1 - (0.536:ℝ)/r)) ≤ 0.536 := by
        have hd : 0 < 1 - (0.536:ℝ)/r := by rw [sub_pos, div_lt_one hr0]; linarith
        rw [div_eq_mul_inv, ← mul_assoc, mul_inv_le_iff₀ hd]
        rw [Nat.cast_sub h1n, Nat.cast_one]
        field_simp
        nlinarith [hr1]
      linarith
    calc Real.exp (-0.536) ≤ pxi r ^ (r-1) := hbase
      _ ≤ pxi r ^ j := pow_le_pow_of_le_one hxi_nonneg hxi_le1 hj
  -- (1)  `ξ^{-r} ≤ 1.87`:  `ξ^{-r} = (ξ^r)⁻¹ ≤ (0.535)⁻¹ ≤ 1.87`.
  have h1 : pxi r ^ (-(r:ℤ)) ≤ 1.87 := by
    have hz : pxi r ^ (-(r:ℤ)) = (pxi r ^ r)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz]
    have hp : 0 < pxi r ^ r := pow_pos hxi_pos r
    have hle : (pxi r ^ r)⁻¹ ≤ (0.535:ℝ)⁻¹ := (inv_le_inv₀ hp (by norm_num)).mpr h2
    have hnum : (0.535:ℝ)⁻¹ ≤ 1.87 := by norm_num
    linarith
  -- (5)  `1.07 ≤ 2ξ^r`:  `2·0.535 = 1.07 ≤ 2ξ^r`.
  have h5 : 1.07 ≤ 2 * pxi r ^ r := by linarith
  exact ⟨h1, h2, h3, h4, h5⟩

end Work.BW
