/-
# `Submission.Work.FIArea6Hecke.R.norm_logDeriv_one_sub_mul_cpow_le`

Euler-factor estimate for the logarithmic derivative of `u ↦ 1 - c·p^{-u}`.

Writing `z := c·(p:ℂ)^{-s}`, the function `u ↦ 1 - c·(p:ℂ)^{-u}` has logarithmic derivative

  `logDeriv (fun u => 1 - c·(p:ℂ)^{-u}) s = z·(log p)/(1 - z)`,

so it suffices to bound `‖z/(1-z)‖`.  The hypothesis says that `z` is either small
(`‖z‖ ≤ 1/2`) or large (`‖z‖ ≥ 4`).  In the small case `‖z/(1-z)‖ ≤ ‖z‖/(1-‖z‖) ≤ 1`, and in the
large case `‖z/(1-z)‖ ≤ ‖z‖/(‖z‖-1) ≤ 4/3`; in both cases the claimed constant `4/3` is enough.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

noncomputable section

/-! ## The derivative of `u ↦ (p : ℂ)^{-u}` and the log-derivative identity -/

/-- `u ↦ (p : ℂ)^{-u}` has derivative `-(log p)·(p : ℂ)^{-w}` at `w`. -/
lemma hasDerivAt_cpow_neg_nat {p : ℕ} (hp : p ≠ 0) (w : ℂ) :
    HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
      (-(((Real.log (p : ℝ)) : ℂ) * ((p : ℂ) ^ (-w)))) w := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hlog : Complex.log ((p : ℂ)) = ((Real.log (p : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)]
  have h := (hasDerivAt_neg w).const_cpow (Or.inl hc)
  rw [hlog] at h
  convert h using 1
  ring

/-- The logarithmic derivative of the Euler factor `1 - c·(p:ℂ)^{-u}`, in closed form. -/
lemma logDeriv_one_sub_mul_cpow_eq {c : ℂ} {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    logDeriv (fun u : ℂ => 1 - c * (p : ℂ) ^ (-u)) s
      = ((Real.log (p : ℝ)) : ℂ) * (c * (p : ℂ) ^ (-s)) / (1 - c * (p : ℂ) ^ (-s)) := by
  rw [logDeriv_apply]
  have h₂ := ((hasDerivAt_cpow_neg_nat hp s).const_mul c).const_sub 1
  rw [h₂.deriv]
  ring

/-! ## Two elementary bounds for `z/(1-z)` -/

/-- If `‖z‖ ≤ 1/2` then `‖z/(1-z)‖ ≤ 1`. -/
lemma norm_div_one_sub_le_of_le_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖z / (1 - z)‖ ≤ 1 := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h, norm_one] at hz; norm_num at hz
  rw [norm_div]
  have hden : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - ‖z‖ by linarith [norm_nonneg z])] at h
    exact h
  have hdenpos : 0 < 1 - ‖z‖ := by linarith [norm_nonneg z]
  have h1 : ‖z‖ / ‖1 - z‖ ≤ ‖z‖ / (1 - ‖z‖) :=
    div_le_div_of_nonneg_left (norm_nonneg z) hdenpos hden
  have h2 : ‖z‖ / (1 - ‖z‖) ≤ 1 := by
    rw [div_le_one hdenpos]
    linarith [hz]
  linarith [h1, h2]

/-- If `4 ≤ ‖z‖` then `‖z/(1-z)‖ ≤ 4/3`. -/
lemma norm_div_one_sub_le_of_four_le {z : ℂ} (hz : 4 ≤ ‖z‖) : ‖z / (1 - z)‖ ≤ 4 / 3 := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h, norm_one] at hz; norm_num at hz
  rw [norm_div]
  have hden : ‖z‖ - 1 ≤ ‖1 - z‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    rw [abs_of_nonpos (show (1 : ℝ) - ‖z‖ ≤ 0 by linarith)] at h
    linarith
  have hdenpos : 0 < ‖z‖ - 1 := by linarith
  have h1 : ‖z‖ / ‖1 - z‖ ≤ ‖z‖ / (‖z‖ - 1) :=
    div_le_div_of_nonneg_left (norm_nonneg z) hdenpos hden
  have h2 : ‖z‖ / (‖z‖ - 1) ≤ 4 / 3 := by
    rw [div_le_iff₀ hdenpos]
    linarith [hz]
  linarith [h1, h2]

/-! ## The target -/

lemma norm_logDeriv_one_sub_mul_cpow_le {c : ℂ} {p : ℕ} {s : ℂ} (hp : 2 ≤ p)
    (h : ‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 ∨ 4 ≤ ‖c * (p : ℂ) ^ (-s)‖) :
    ‖logDeriv (fun u : ℂ => 1 - c * (p : ℂ) ^ (-u)) s‖ ≤ (4 / 3) * Real.log p := by
  have hp1 : 1 < p := by omega
  have hp0 : p ≠ 0 := by omega
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1.le)
  rw [logDeriv_one_sub_mul_cpow_eq hp0 s]
  have hkey : ‖(c * (p : ℂ) ^ (-s)) / (1 - c * (p : ℂ) ^ (-s))‖ ≤ 4 / 3 := by
    rcases h with h1 | h1
    · exact le_trans (norm_div_one_sub_le_of_le_half h1) (by norm_num)
    · exact norm_div_one_sub_le_of_four_le h1
  calc ‖((Real.log (p : ℝ)) : ℂ) * (c * (p : ℂ) ^ (-s)) / (1 - c * (p : ℂ) ^ (-s))‖
      = Real.log (p : ℝ) * ‖(c * (p : ℂ) ^ (-s)) / (1 - c * (p : ℂ) ^ (-s))‖ := by
        rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog0]
    _ ≤ Real.log (p : ℝ) * (4 / 3) := mul_le_mul_of_nonneg_left hkey hlog0
    _ = (4 / 3) * Real.log (p : ℝ) := by ring

end

end Work.FIArea6Hecke.R
