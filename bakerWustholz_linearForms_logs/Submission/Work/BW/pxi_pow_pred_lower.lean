import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Elementary logarithm bound: for `0 ≤ a ≤ 1` and `2 ≤ n`,
`-a ≤ (n-1) · log (1 - a/n)`.  This is the numerical heart of the lower bound
`exp(-0.536) ≤ pxi r ^ (r-1)` for `r ≥ 2`. -/
theorem mul_log_one_sub_div_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    -a ≤ ((n : ℝ) - 1) * Real.log (1 - a / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := by omega
    exact_mod_cast h
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set u : ℝ := a / (n : ℝ) with hu
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hnR]
    linarith
  have h1u : (0 : ℝ) < 1 - u := by linarith
  -- key arithmetic: `(n-1)·u ≤ a·(1-u)`
  have hnum : ((n : ℝ) - 1) * a ≤ a * ((n : ℝ) - a) := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hdiv : ((n : ℝ) - 1) * a / (n : ℝ) ≤ a * ((n : ℝ) - a) / (n : ℝ) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hnR)
  have e1 : ((n : ℝ) - 1) * u = ((n : ℝ) - 1) * a / (n : ℝ) := by
    rw [hu, mul_div_assoc]
  have e2 : a * (1 - u) = a * ((n : ℝ) - a) / (n : ℝ) := by
    have hnu : 1 - u = ((n : ℝ) - a) / (n : ℝ) := by
      rw [hu, sub_div, div_self (ne_of_gt hnR)]
    rw [hnu, mul_div_assoc]
  have hle : ((n : ℝ) - 1) * u ≤ a * (1 - u) := by rw [e1, e2]; exact hdiv
  -- logarithm bound: `1 - (1-u)⁻¹ ≤ log (1-u)`
  have hlog : 1 - (1 - u)⁻¹ ≤ Real.log (1 - u) := by
    have hpos : (0 : ℝ) < (1 - u)⁻¹ := by rw [inv_pos]; linarith
    have h := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_inv] at h
    linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hmul : ((n : ℝ) - 1) * (1 - (1 - u)⁻¹) ≤ ((n : ℝ) - 1) * Real.log (1 - u) :=
    mul_le_mul_of_nonneg_left hlog hn1
  -- arithmetic: `(n-1)·((1-u)⁻¹ - 1) ≤ a`
  have hident : (1 - u) * ((1 - u)⁻¹ - 1) = u := by
    rw [mul_sub, mul_inv_cancel₀ (ne_of_gt h1u), mul_one]
    ring
  have hkey : ((n : ℝ) - 1) * ((1 - u)⁻¹ - 1) ≤ a := by
    apply le_of_mul_le_mul_right _ h1u
    calc ((n : ℝ) - 1) * ((1 - u)⁻¹ - 1) * (1 - u)
        = ((n : ℝ) - 1) * ((1 - u) * ((1 - u)⁻¹ - 1)) := by ring
      _ = ((n : ℝ) - 1) * u := by rw [hident]
      _ ≤ a * (1 - u) := hle
  have hkey2 : -a ≤ ((n : ℝ) - 1) * (1 - (1 - u)⁻¹) := by
    have : ((n : ℝ) - 1) * (1 - (1 - u)⁻¹) = -(((n : ℝ) - 1) * ((1 - u)⁻¹ - 1)) := by ring
    rw [this]; linarith
  have hres : -a ≤ ((n : ℝ) - 1) * Real.log (1 - u) := le_trans hkey2 hmul
  rwa [hu] at hres

theorem pxi_pow_pred_lower {r : ℕ} (hr : 2 ≤ r) : Real.exp (-0.536) ≤ Work.BW.pxi r ^ (r - 1) := by
  have hlog := mul_log_one_sub_div_ge (a := 0.536) (by norm_num) (by norm_num) hr
  have hlog' : -0.536 ≤ ((r : ℝ) - 1) * Real.log (Work.BW.pxi r) := by
    rw [pxi]
    exact hlog
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    have h1 : 1 ≤ r := by omega
    push_cast [h1]; ring
  have hexp : Real.exp (((r : ℝ) - 1) * Real.log (Work.BW.pxi r)) = Work.BW.pxi r ^ (r - 1) := by
    rw [← hcast, Real.exp_nat_mul, Real.exp_log (pxi_pos hr)]
  calc Real.exp (-0.536) ≤ Real.exp (((r : ℝ) - 1) * Real.log (Work.BW.pxi r)) :=
        Real.exp_le_exp.mpr hlog'
    _ = Work.BW.pxi r ^ (r - 1) := hexp

end Work.BW
