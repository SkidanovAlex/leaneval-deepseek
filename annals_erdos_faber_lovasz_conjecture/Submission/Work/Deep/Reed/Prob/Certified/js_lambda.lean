/-
# Choosing the exponent `λ`

For every `r ∈ (0,1]` there is an exponent `λ ∈ [0,1]` with

`exp ((1 - λ)^2 / 4) * r ^ (-λ) ≤ 2 - r`.

Writing `r = exp (-t)` with `t = -log r ≥ 0`, the left-hand side is
`exp ((1-λ)^2/4 + λ t)`, and the choice of `λ` optimising the exponent is
`λ = max (0, 1 - 2t)`:

* for `t ≤ 1/2`, `λ = 1 - 2t` and the exponent is exactly `t - t²`, so the
  claim reduces to `exp (t - t²) ≤ 2 - exp (-t)`;
* for `t ≥ 1/2`, `λ = 0` and the claim reduces to `exp (1/4) + exp (-1/2) ≤ 2`.

Both are elementary.  The first is proved by showing that
`t ↦ log (2 - exp (-t)) - (t - t²)` has nonnegative derivative on `[0,1/2]`
and vanishes at `0`; the derivative estimate uses only `1 + x ≤ exp x`
(in the form `exp x ≤ 1/(1-x)` for `x < 1`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option autoImplicit false

namespace Work.Deep.Reed.Prob.Certified

/-- For `t < 1`, `exp t ≤ 1 / (1 - t)`. -/
private theorem exp_le_one_div_one_sub {t : ℝ} (ht : t < 1) : Real.exp t ≤ 1 / (1 - t) := by
  have h0 : 0 < 1 - t := by linarith
  have h1 : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith
  rw [le_div_iff₀ h0, mul_comm (Real.exp t) (1 - t)]
  calc (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- `exp (1/4) ≤ 4/3`. -/
private theorem exp_quarter_le : Real.exp (1/4) ≤ 4/3 := by
  have h := exp_le_one_div_one_sub (t := (1/4 : ℝ)) (by norm_num)
  have e : (1 : ℝ) / (1 - 1/4) = 4/3 := by norm_num
  rwa [e] at h

/-- `exp (-1/2) ≤ 2/3`. -/
private theorem exp_neg_half_le : Real.exp (-(1/2 : ℝ)) ≤ 2/3 := by
  have h := exp_le_one_div_one_sub (t := -(1/2 : ℝ)) (by norm_num)
  have e : (1 : ℝ) / (1 - -(1/2)) = 2/3 := by norm_num
  rwa [e] at h

/-- `exp (1/4) + exp (-1/2) ≤ 2`. -/
private theorem exp_quarter_add_exp_neg_half_le_two :
    Real.exp (1/4) + Real.exp (-(1/2 : ℝ)) ≤ 2 := by
  linarith [exp_quarter_le, exp_neg_half_le]

/-- `0 < 2 - exp (-t)` for `t ≥ 0`. -/
private theorem two_sub_exp_neg_pos {t : ℝ} (ht : 0 ≤ t) : 0 < 2 - Real.exp (-t) := by
  have h : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- The auxiliary function whose monotonicity gives `t - t² ≤ log (2 - exp (-t))`. -/
private noncomputable def Hf (t : ℝ) : ℝ := Real.log (2 - Real.exp (-t)) - (t - t ^ 2)

private theorem Hf_zero : Hf 0 = 0 := by
  simp only [Hf, neg_zero, Real.exp_zero]
  norm_num

private theorem hasDerivAt_Hf (x : ℝ) (hx : 2 - Real.exp (-x) ≠ 0) :
    HasDerivAt Hf (Real.exp (-x) / (2 - Real.exp (-x)) - (1 - 2 * x)) x := by
  have h2 : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-(Real.exp (-x))) x := by
    have h := h2.exp
    simpa only [neg_one_mul, mul_neg_one] using h
  have h1 : HasDerivAt (fun t : ℝ => 2 - Real.exp (-t)) (Real.exp (-x)) x := by
    have h := h3.const_sub 2
    simpa only [neg_neg] using h
  have h4 : HasDerivAt (fun t : ℝ => Real.log (2 - Real.exp (-t)))
      (Real.exp (-x) / (2 - Real.exp (-x))) x := h1.log hx
  have h6 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h5 : HasDerivAt (fun t : ℝ => t - t ^ 2) (1 - 2 * x) x :=
    (hasDerivAt_id x).sub h6
  exact h4.sub h5

/-- The derivative of `Hf` is nonnegative on `[0,1/2]`. -/
private theorem deriv_Hf_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    0 ≤ Real.exp (-x) / (2 - Real.exp (-x)) - (1 - 2 * x) := by
  have hd : 0 < 2 - Real.exp (-x) := two_sub_exp_neg_pos hx0
  -- the one crucial estimate `(1 - 2x) exp x ≤ 1 - x`
  have key : (1 - 2 * x) * Real.exp x ≤ 1 - x := by
    rcases lt_or_eq_of_le hx1 with h | h
    · have h2x : 0 ≤ 1 - 2 * x := by linarith
      have he : Real.exp x ≤ 1 / (1 - x) := exp_le_one_div_one_sub (by linarith)
      have e1 : (1 - 2 * x) * Real.exp x ≤ (1 - 2 * x) * (1 / (1 - x)) :=
        mul_le_mul_of_nonneg_left he h2x
      have e2 : (1 - 2 * x) * (1 / (1 - x)) ≤ 1 - x := by
        have hpos : 0 < 1 - x := by linarith
        rw [mul_one_div, div_le_iff₀ hpos]
        nlinarith [sq_nonneg x]
      linarith
    · subst h
      norm_num
  -- rewriting it in the form needed below
  have hN : 1 - 2 * x ≤ (1 - x) * Real.exp (-x) := by
    have hmul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h := mul_le_mul_of_nonneg_right key (Real.exp_pos (-x)).le
    rw [mul_assoc, hmul, mul_one] at h
    exact h
  rw [sub_nonneg, le_div_iff₀ hd]
  have e : (1 - 2 * x) * (2 - Real.exp (-x))
      = 2 * (1 - 2 * x) - 2 * ((1 - x) * Real.exp (-x)) + Real.exp (-x) := by ring
  rw [e]
  linarith

private theorem Hf_mono : MonotoneOn Hf (Set.Icc 0 (1/2)) := by
  -- differentiability on an open neighbourhood of `[0,1/2]`
  have hdiff : DifferentiableOn ℝ Hf (Set.Ioo (-(1/4)) 1) := by
    intro x hx
    have hlt : Real.exp (-x) ≤ 4/3 := by
      have h : Real.exp (-x) ≤ Real.exp (1/4) := by
        apply Real.exp_le_exp.mpr
        linarith [hx.1]
      linarith [exp_quarter_le]
    have hx2 : 2 - Real.exp (-x) ≠ 0 := by
      have : Real.exp (-x) < 2 := by linarith
      linarith
    exact (hasDerivAt_Hf x hx2).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (1/2)) ?_ ?_ ?_
  · refine hdiff.continuousOn.mono ?_
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [interior_Icc]
    refine hdiff.mono ?_
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [interior_Icc]
    intro x hx
    have hx2 : 2 - Real.exp (-x) ≠ 0 := ne_of_gt (two_sub_exp_neg_pos hx.1.le)
    rw [(hasDerivAt_Hf x hx2).deriv]
    exact deriv_Hf_nonneg hx.1.le hx.2.le

/-- For `t ∈ [0,1/2]`, `exp (t - t²) ≤ 2 - exp (-t)`. -/
private theorem exp_sub_sq_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    Real.exp (t - t ^ 2) ≤ 2 - Real.exp (-t) := by
  have hmem : t ∈ Set.Icc (0 : ℝ) (1/2) := ⟨ht0, ht1⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := ⟨le_refl _, by norm_num⟩
  have hmono := Hf_mono hmem0 hmem ht0
  rw [Hf_zero, Hf] at hmono
  exact (Real.le_log_iff_exp_le (two_sub_exp_neg_pos ht0)).mp (by linarith)

theorem js_lambda {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ Real.exp ((1 - lam) ^ 2 / 4) * r ^ (-lam) ≤ 2 - r := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, Real.log r = -t := ⟨-Real.log r, by ring⟩
  have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
  have ht0 : 0 ≤ t := by linarith
  have htr : r = Real.exp (-t) := by
    rw [← ht, Real.exp_log hr0]
  have hrpow : ∀ lam : ℝ, r ^ (-lam) = Real.exp (lam * t) := by
    intro lam
    rw [Real.rpow_def_of_pos hr0, ht, neg_mul_neg, mul_comm t lam]
  by_cases h : t ≤ 1/2
  · refine ⟨1 - 2 * t, by linarith, by linarith, ?_⟩
    rw [hrpow, htr, ← Real.exp_add]
    have e1 : (1 - (1 - 2 * t)) ^ 2 / 4 + (1 - 2 * t) * t = t - t ^ 2 := by ring
    rw [e1]
    exact exp_sub_sq_le ht0 h
  · refine ⟨0, le_refl 0, by norm_num, ?_⟩
    have h1 : Real.exp (-t) ≤ Real.exp (-(1/2 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (1/4) ≤ 2 - Real.exp (-t) := by
      linarith [h1, exp_quarter_add_exp_neg_half_le_two]
    simp only [sub_zero, pow_two, mul_one, neg_zero, Real.rpow_zero]
    rw [htr]
    exact h3

end Work.Deep.Reed.Prob.Certified
