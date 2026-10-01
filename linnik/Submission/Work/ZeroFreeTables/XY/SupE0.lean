/-
# ZeroFreeTables/XY/SupE0

The single-estimate bound `E₀(λ) ≤ 3/200` for `0 ≤ λ ≤ 628/1000`, where
`E₀(λ) = ∫₀^{3/4} g(x)(cosh(λx) - 1) dx` and `g = xyG` is HB's auxiliary function
`g(x) = (4/3)(1 - (16/9)x²)` on `[0, 3/4]`.

Writing `cosh(λx) - 1 ≤ (λx)²/2 + (λx)⁴/20` (valid since `λx ≤ 0.471 ≤ 1/2`, cf. the
Taylor bound `cosh_sub_one_le_quad`), the integral is bounded by
`(λ²/2)·∫₀^{3/4} g x² + (λ⁴/20)·∫₀^{3/4} g x⁴ = 3λ²/80 + 81λ⁴/89600 ≤ 3/200`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- Taylor bound: for `t ∈ [0, 1/2]`, `cosh t - 1 ≤ t²/2 + t⁴/20`.
(The exact series has coefficient `1/24` of `t⁴`; the slack is absorbed by `t ≤ 1/2`.) -/
lemma cosh_sub_one_le_quad (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1/2) :
    Real.cosh t - 1 ≤ t^2/2 + t^4/20 := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hnt1 : |-t| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have hreprP : |t|^5 * ((5:ℕ).succ / ((5:ℕ).factorial * (5:ℕ)) : ℝ) = t^5/100 := by
    rw [abs_of_nonneg h0]
    norm_num
    ring
  have hreprN : |-t|^5 * ((5:ℕ).succ / ((5:ℕ).factorial * (5:ℕ)) : ℝ) = t^5/100 := by
    rw [abs_neg, abs_of_nonneg h0]
    norm_num
    ring
  have hp : Real.exp t ≤ (∑ m ∈ Finset.range 5, t^m/(m.factorial:ℝ)) + t^5/100 := by
    have h := Real.exp_bound ht1 (n := 5) (by norm_num)
    have hle := (abs_sub_le_iff.1 h).1
    rw [hreprP] at hle
    linarith
  have hm : Real.exp (-t) ≤ (∑ m ∈ Finset.range 5, (-t)^m/(m.factorial:ℝ)) + t^5/100 := by
    have h := Real.exp_bound hnt1 (n := 5) (by norm_num)
    have hle := (abs_sub_le_iff.1 h).1
    rw [hreprN] at hle
    linarith
  have hsum : (∑ m ∈ Finset.range 5, t^m/(m.factorial:ℝ))
      + (∑ m ∈ Finset.range 5, (-t)^m/(m.factorial:ℝ)) = 2 + t^2 + t^4/12 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
    ring
  have hstep : Real.cosh t ≤ 1 + t^2/2 + t^4/24 + t^5/100 := by
    rw [Real.cosh_eq]
    linarith [hp, hm, hsum]
  have h4 : (0:ℝ) ≤ t^4 := by positivity
  have h5 : t^5 ≤ t^4/2 := by
    have := mul_le_mul_of_nonneg_left h1 h4
    nlinarith [this]
  have h5' : t^5/100 ≤ t^4/200 := by linarith [h5]
  linarith [hstep, h5']

/-- `∫₀^{3/4} x² g(x) dx = 3/40`. -/
lemma xyG_sq_integral :
    (∫ x in (0:ℝ)..(3/4), xyG x * x^2) = 3/40 := by
  have hcongr : (∫ x in (0:ℝ)..(3/4), xyG x * x^2)
      = ∫ x in (0:ℝ)..(3/4), (4/3 * (1 - 16/9 * x^2)) * x^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/4)] at hx
    show xyG x * x^2 = (4/3 * (1 - 16/9 * x^2)) * x^2
    rw [xyG_eq_poly x hx]
  rw [hcongr]
  have hsplit : (∫ x in (0:ℝ)..(3/4), (4/3 * (1 - 16/9 * x^2)) * x^2)
      = (4/3) * (∫ x in (0:ℝ)..(3/4), x^2) - (64/27) * (∫ x in (0:ℝ)..(3/4), x^4) := by
    rw [show (fun x : ℝ => (4/3 * (1 - 16/9 * x^2)) * x^2)
        = (fun x : ℝ => (4/3) * x^2 - (64/27) * x^4) from by funext x; ring]
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by continuity : Continuous (fun x : ℝ => (4/3) * x^2)) 0 (3/4))
      (Continuous.intervalIntegrable (by continuity : Continuous (fun x : ℝ => (64/27) * x^4)) 0 (3/4)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit, integral_pow, integral_pow]
  norm_num

/-- `∫₀^{3/4} x⁴ g(x) dx = 81/4480`. -/
lemma xyG_four_integral :
    (∫ x in (0:ℝ)..(3/4), xyG x * x^4) = 81/4480 := by
  have hcongr : (∫ x in (0:ℝ)..(3/4), xyG x * x^4)
      = ∫ x in (0:ℝ)..(3/4), (4/3 * (1 - 16/9 * x^2)) * x^4 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/4)] at hx
    show xyG x * x^4 = (4/3 * (1 - 16/9 * x^2)) * x^4
    rw [xyG_eq_poly x hx]
  rw [hcongr]
  have hsplit : (∫ x in (0:ℝ)..(3/4), (4/3 * (1 - 16/9 * x^2)) * x^4)
      = (4/3) * (∫ x in (0:ℝ)..(3/4), x^4) - (64/27) * (∫ x in (0:ℝ)..(3/4), x^6) := by
    rw [show (fun x : ℝ => (4/3 * (1 - 16/9 * x^2)) * x^4)
        = (fun x : ℝ => (4/3) * x^4 - (64/27) * x^6) from by funext x; ring]
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by continuity : Continuous (fun x : ℝ => (4/3) * x^4)) 0 (3/4))
      (Continuous.intervalIntegrable (by continuity : Continuous (fun x : ℝ => (64/27) * x^6)) 0 (3/4)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit, integral_pow, integral_pow]
  norm_num

theorem SupE0 {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 628/1000) :
    Work.ZeroFreeTables.XY.E0c lam ≤ 3/200 := by
  rw [E0c]
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) (3/4),
      xyG x * (Real.cosh (lam*x) - 1) ≤ xyG x * ((lam*x)^2/2 + (lam*x)^4/20) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hlx1 : lam * x ≤ 1/2 := by
      have h2 : lam * x ≤ ((628:ℝ)/1000) * (3/4) := mul_le_mul h1 hx.2 hx0 (by norm_num)
      have h3 : ((628:ℝ)/1000) * (3/4) = 471/1000 := by norm_num
      rw [h3] at h2; linarith
    have hlx0 : 0 ≤ lam * x := mul_nonneg h0 hx0
    exact mul_le_mul_of_nonneg_left (cosh_sub_one_le_quad (lam*x) hlx0 hlx1) (xyG_nonneg x)
  have hIf : IntervalIntegrable (fun x : ℝ => xyG x * (Real.cosh (lam*x) - 1)) volume (0:ℝ) (3/4) :=
    (xyG_cont.mul (by continuity : Continuous (fun x : ℝ => Real.cosh (lam*x) - 1))).intervalIntegrable 0 (3/4)
  have hIg : IntervalIntegrable (fun x : ℝ => xyG x * ((lam*x)^2/2 + (lam*x)^4/20)) volume (0:ℝ) (3/4) :=
    (xyG_cont.mul (by continuity : Continuous (fun x : ℝ => (lam*x)^2/2 + (lam*x)^4/20))).intervalIntegrable 0 (3/4)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 3/4 by norm_num) hIf hIg hpt
  have hupper : (∫ x in (0:ℝ)..(3/4), xyG x * ((lam*x)^2/2 + (lam*x)^4/20))
      = lam^2/2 * (3/40) + lam^4/20 * (81/4480) := by
    have hcongr : (∫ x in (0:ℝ)..(3/4), xyG x * ((lam*x)^2/2 + (lam*x)^4/20))
        = ∫ x in (0:ℝ)..(3/4), (lam^2/2) * (xyG x * x^2) + (lam^4/20) * (xyG x * x^4) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hI1 : IntervalIntegrable (fun x : ℝ => (lam^2/2) * (xyG x * x^2)) volume (0:ℝ) (3/4) :=
      ((continuous_const : Continuous (fun _ : ℝ => lam^2/2)).mul
        (xyG_cont.mul (by continuity : Continuous (fun x : ℝ => x^2)))).intervalIntegrable 0 (3/4)
    have hI2 : IntervalIntegrable (fun x : ℝ => (lam^4/20) * (xyG x * x^4)) volume (0:ℝ) (3/4) :=
      ((continuous_const : Continuous (fun _ : ℝ => lam^4/20)).mul
        (xyG_cont.mul (by continuity : Continuous (fun x : ℝ => x^4)))).intervalIntegrable 0 (3/4)
    rw [hcongr, intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, xyG_sq_integral, xyG_four_integral]
  refine le_trans hmono ?_
  rw [hupper]
  have hl : lam ≤ 157/250 := by linarith [h1]
  have h2 : lam^2 ≤ (157/250)^2 := by
    simpa [pow_two] using mul_self_le_mul_self h0 hl
  have h4 : lam^4 ≤ (157/250)^4 := by
    have hh := mul_le_mul h2 h2 (by positivity) (by norm_num)
    nlinarith [hh]
  have step1 : lam^2/2*(3/40) ≤ (157/250)^2/2*(3/40) := by nlinarith [h2]
  have step2 : lam^4/20*(81/4480) ≤ (157/250)^4/20*(81/4480) := by nlinarith [h4]
  have hnum : (157/250)^2/2*(3/40) + (157/250)^4/20*(81/4480) ≤ 3/200 := by norm_num
  linarith

end Work.ZeroFreeTables.XY
