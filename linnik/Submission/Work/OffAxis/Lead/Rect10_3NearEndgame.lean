import Mathlib
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.OffAxis.tf72f_moment_step
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone

/-!
# `Work.OffAxis.Rect10_3NearEndgame`

The numerical endgame of the off-axis `Rect10_3` route: from Heath-Brown's (10.6)

`F(-λ₁) - F(0) - F(λ₂-λ₁) - F(λ₃-λ₁) + f(0)(7/6 + 8ε') ≥ 0`

for the Lemma 7.2 test function at `λ = 6/7`, together with `0 ≤ λ₁ ≤ λ₂ ≤ λ₃ ≤ 6/7`,
one gets `λ₃ ≥ 6/7 - 100000 ε'`.

The whole content is the *quantitative* positivity of the `F`-method gap

`G lam = F (-lam) - 2 F (6/7 - lam) = tf72fPhi lam = ∫_0^{7/3} exp (lam t) * tf72fK t dt`

for the signed kernel `tf72fK t = (1 - 2 exp (-(6/7) t)) * tf72f (6/7) t`:

`(104/66825) * (6/7 - lam) ≤ G (6/7) - G lam`   for `0 ≤ lam ≤ 6/7`.

Indeed, the hypothesis bounds the left hand side above by `G lam - G (6/7) + 8 f(0) ε'`
(monotonicity of `F` and the identity `f(0)(7/6) = 3F(0) - F(-6/7)`), so the hypothesis forces
`(104/66825)(6/7 - λ₁) ≤ 8 f(0) ε'` and hence `6/7 - λ₃ ≤ (8 f(0) · 66825/104) ε' ≤ 100000 ε'`.

## How the gap bound is produced

With `τ = (7/6) log 2` (the kernel's single sign change) and `κ = ∫_0^{7/3} t * tf72fK t`, freezing
the weight `exp (x t)` at `t = τ` on the negative part `[0,τ]` of the kernel and at the same point
on its positive part `[τ,7/3]` gives `exp (x τ) * κ ≤ tf72fPhi' x` for `x ≥ 0`; since
`exp (x τ) ≥ 1` and `κ ≥ 104/66825` (quartic Taylor bound for `exp` plus the moments of
`tf72f (6/7)`), the derivative of `s ↦ tf72fPhi s - (104/66825) s` is non-negative on `[0,∞)`,
so that function is monotone by `monotoneOn_of_deriv_nonneg`.
-/

open scoped Interval
open MeasureTheory

namespace Work.OffAxis.Lead

open Work.ZeroFreeTables

/-! ## 1.  The signed kernel `tf72fK` and its single sign change at `τ = (7/6) log 2` -/

/-- The point where `tf72fK` changes sign: `exp ((6/7) t) = 2`. -/
private noncomputable def tau72 : ℝ := (7/6) * Real.log 2

private lemma tau72_nonneg : 0 ≤ tau72 := by
  have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [tau72]; linarith

/-- On `[0, τ]` the kernel `tf72fK` is non-positive. -/
private lemma tf72fK_nonpos_of_le_tau (t : ℝ) (ht : t ≤ tau72) : tf72fK t ≤ 0 := by
  have hexp1 : Real.exp ((6/7) * t) ≤ 2 := by
    have h : (6/7) * t ≤ (6/7) * tau72 := mul_le_mul_of_nonneg_left ht (by norm_num)
    have h2 : Real.exp ((6/7) * t) ≤ Real.exp ((6/7) * tau72) := Real.exp_le_exp.mpr h
    rwa [show (6/7) * tau72 = Real.log 2 by rw [tau72]; ring,
      Real.exp_log (by norm_num)] at h2
  have hone : 1 ≤ 2 * Real.exp (-(6/7) * t) := by
    have hmul : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) = 1 := by
      rw [← Real.exp_add, show -(6/7) * t + (6/7) * t = 0 by ring, Real.exp_zero]
    have hle : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t)
        ≤ Real.exp (-(6/7) * t) * 2 :=
      mul_le_mul_of_nonneg_left hexp1 (Real.exp_pos _).le
    linarith
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  unfold tf72fK
  nlinarith [hone, hf]

/-- On `[τ, ∞)` the kernel `tf72fK` is non-negative. -/
private lemma tf72fK_nonneg_of_tau_le (t : ℝ) (ht : tau72 ≤ t) : 0 ≤ tf72fK t := by
  have hexp1 : 2 ≤ Real.exp ((6/7) * t) := by
    have h : (6/7) * tau72 ≤ (6/7) * t := mul_le_mul_of_nonneg_left ht (by norm_num)
    have h2 : Real.exp ((6/7) * tau72) ≤ Real.exp ((6/7) * t) := Real.exp_le_exp.mpr h
    rwa [show (6/7) * tau72 = Real.log 2 by rw [tau72]; ring,
      Real.exp_log (by norm_num)] at h2
  have hone : 2 * Real.exp (-(6/7) * t) ≤ 1 := by
    have hmul : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) = 1 := by
      rw [← Real.exp_add, show -(6/7) * t + (6/7) * t = 0 by ring, Real.exp_zero]
    have hle : Real.exp (-(6/7) * t) * 2
        ≤ Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) :=
      mul_le_mul_of_nonneg_left hexp1 (Real.exp_pos _).le
    linarith
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  unfold tf72fK
  nlinarith [hone, hf]

/-- `tf72fK` is continuous on the support `[0, 7/3]`. -/
private lemma tf72fK_continuousOn_Icc : ContinuousOn tf72fK (Set.Icc (0:ℝ) (7/3)) := by
  have hfcont : ContinuousOn (tf72f (6/7)) (Set.Icc (0:ℝ) (7/3)) :=
    (tf72f_cont (6/7) (by norm_num)).mono (fun t ht => ht.1)
  have h1 : Continuous (fun t : ℝ => (1:ℝ) - 2 * Real.exp (-(6/7) * t)) := by fun_prop
  unfold tf72fK
  exact h1.continuousOn.mul hfcont

/-! ## 2.  The frozen-weight lower bound for the derivative `tf72fPhi'` -/

/-- **The derivative of the gap functional dominates its value at `0`.**  Freezing the weight
`exp (x t)` at the kernel's sign-change point `τ` exhibits
`∫ t * tf72fK t ≤ ∫ t * (exp (x t) * tf72fK t) = tf72fPhi' x` for `x ≥ 0`. -/
private lemma tf72fPhi_deriv_lower (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0:ℝ)..(7/3), t * tf72fK t)
      ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) := by
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (7/3),
      t * (Real.exp (x * tau72) * tf72fK t) ≤ t * (Real.exp (x * t) * tf72fK t) := by
    intro t ht
    rcases lt_or_ge t tau72 with h1 | h1
    · have hexp : Real.exp (x * t) ≤ Real.exp (x * tau72) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1.le hx)
      have hK : tf72fK t ≤ 0 := tf72fK_nonpos_of_le_tau t h1.le
      have htK : t * tf72fK t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hK
      calc t * (Real.exp (x * tau72) * tf72fK t)
          = Real.exp (x * tau72) * (t * tf72fK t) := by ring
        _ ≤ Real.exp (x * t) * (t * tf72fK t) := mul_le_mul_of_nonpos_right hexp htK
        _ = t * (Real.exp (x * t) * tf72fK t) := by ring
    · have hexp : Real.exp (x * tau72) ≤ Real.exp (x * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hx)
      have hK : 0 ≤ tf72fK t := tf72fK_nonneg_of_tau_le t h1
      have ht0 : 0 ≤ t := le_trans tau72_nonneg h1
      have htK : 0 ≤ t * tf72fK t := mul_nonneg ht0 hK
      calc t * (Real.exp (x * tau72) * tf72fK t)
          = Real.exp (x * tau72) * (t * tf72fK t) := by ring
        _ ≤ Real.exp (x * t) * (t * tf72fK t) := mul_le_mul_of_nonneg_right hexp htK
        _ = t * (Real.exp (x * t) * tf72fK t) := by ring
  have hi1 : IntervalIntegrable (fun t : ℝ => t * (Real.exp (x * tau72) * tf72fK t))
      volume (0:ℝ) (7/3) :=
    (continuous_id.continuousOn.mul (continuousOn_const.mul tf72fK_continuousOn_Icc))
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hi2 : IntervalIntegrable (fun t : ℝ => t * (Real.exp (x * t) * tf72fK t))
      volume (0:ℝ) (7/3) :=
    (continuous_id.continuousOn.mul
      (((by fun_prop : Continuous fun t : ℝ => Real.exp (x * t))).continuousOn.mul
        tf72fK_continuousOn_Icc)) |>.intervalIntegrable_of_Icc (by norm_num)
  have hmono : (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau72) * tf72fK t))
      ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) :=
    intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 7/3) hi1 hi2 hpt
  have hL : (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau72) * tf72fK t))
      = Real.exp (x * tau72) * (∫ t in (0:ℝ)..(7/3), t * tf72fK t) := by
    rw [show (fun t : ℝ => t * (Real.exp (x * tau72) * tf72fK t))
        = (fun t : ℝ => Real.exp (x * tau72) * (t * tf72fK t)) from by funext t; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hL] at hmono
  have hexp_ge_one : 1 ≤ Real.exp (x * tau72) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (mul_nonneg hx tau72_nonneg)
  have hκ : 0 ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t := tf72fK_t_moment_nonneg
  calc (∫ t in (0:ℝ)..(7/3), t * tf72fK t)
      ≤ Real.exp (x * tau72) * (∫ t in (0:ℝ)..(7/3), t * tf72fK t) := by
        nlinarith [hexp_ge_one, hκ]
    _ ≤ _ := hmono

/-! ## 3.  The first moment of the kernel is at least `104/66825` -/

/-- The signed kernel `tf72fK` has first moment at least `104/66825`: the quartic Taylor bound
`exp (-x) ≤ 1 - x + x²/2 - x³/6 + x⁴/24` gives the pointwise bound with the quintic
`-t + (12/7) t² - (36/49) t³ + (72/343) t⁴ - (108/2401) t⁵`, whose integral against
`tf72f (6/7)` is exactly `104/66825` (this is the quantitative form of
`tf72fK_t_moment_nonneg`). -/
private lemma tf72fK_t_moment_lower :
    (104/66825 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t := by
  have hab : (0:ℝ) ≤ 7/3 := by norm_num
  have hcontf : ContinuousOn (fun t : ℝ => tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) := by
    refine (tf72f_cont (6/7) (by norm_num)).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ht.1
  have hcontK : ContinuousOn (fun t : ℝ => t * tf72fK t) (Set.uIcc (0:ℝ) (7/3)) := by
    have hexp : Continuous (fun t : ℝ => (1:ℝ) - 2 * Real.exp (-(6/7) * t)) := by fun_prop
    have h : ContinuousOn (fun t : ℝ => (t * ((1:ℝ) - 2 * Real.exp (-(6/7) * t)))
        * tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) :=
      (continuous_id.continuousOn.mul hexp.continuousOn).mul hcontf
    simpa only [tf72fK, mul_assoc] using h
  have hcontL : ContinuousOn (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t))
      (Set.uIcc (0:ℝ) (7/3)) :=
    (by fun_prop : Continuous (fun t : ℝ => ((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5))).continuousOn.mul hcontf
  have hintK : IntervalIntegrable (fun t : ℝ => t * tf72fK t) volume (0:ℝ) (7/3) :=
    hcontK.intervalIntegrable
  have hintL : IntervalIntegrable (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2
      + (-(36/49)) * t^3 + (72/343) * t^4 + (-(108/2401)) * t^5)
      * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    hcontL.intervalIntegrable
  have hle := intervalIntegral.integral_mono_on hab hintL hintK
    (fun t ht => tf72fK_t_moment_pointwise t (Set.mem_Icc.mp ht).1)
  have hval : (∫ t in (0:ℝ)..(7/3), (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t)) = 104/66825 :=
    tf72fK_moment_lincomb
  linarith [hle, hval]

/-! ## 4.  The quantitative gap -/

/-- **The quantitative `F`-method gap for HB Lemma 7.2 at `λ = 6/7`**:
`(104/66825) * (6/7 - lam) ≤ tf72fPhi (6/7) - tf72fPhi lam` for `0 ≤ lam ≤ 6/7`. -/
theorem tf72fPhi_gap_quant : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 6/7 →
    (104/66825 : ℝ) * (6/7 - lam) ≤ tf72fPhi (6/7) - tf72fPhi lam := by
  intro lam h0 h1
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => tf72fPhi y - (104/66825 : ℝ) * y)
      ((∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t)) - 104/66825) x := by
    intro x
    exact (tf72fK_hasDerivAt x).sub (hasDerivAt_const_mul (x := x) (104/66825 : ℝ))
  have hcont : ContinuousOn (fun y : ℝ => tf72fPhi y - (104/66825 : ℝ) * y) (Set.Ici 0) := by
    intro x _
    exact (hderiv x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => tf72fPhi y - (104/66825 : ℝ) * y)
      (interior (Set.Ici 0)) := by
    intro x _
    exact ((hderiv x).differentiableAt).differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff (fun x hx => by
    rw [(hderiv x).deriv]
    have hx0 : 0 ≤ x := Set.mem_Ici.mp (interior_subset hx)
    have h1' := tf72fPhi_deriv_lower x hx0
    have h2' := tf72fK_t_moment_lower
    linarith)
  have hmem := hmono (show lam ∈ Set.Ici (0:ℝ) from h0)
    (show (6/7 : ℝ) ∈ Set.Ici (0:ℝ) by norm_num) h1
  linarith

/-! ## 5.  The endgame -/

theorem Rect10_3NearEndgame : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1/1000 → ∀ lam₁ lam₂ lam₃ : ℝ,
    0 ≤ lam₁ → lam₁ ≤ lam₂ → lam₂ ≤ lam₃ → lam₃ ≤ 6/7 →
    (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F (-lam₁)
      - (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F 0
      - (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F (lam₂ - lam₁)
      - (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F (lam₃ - lam₁)
      + (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).f 0 * (7/6 + 8 * ε') ≥ 0 →
    6/7 - 100000 * ε' ≤ lam₃ := by
  intro ε' hε' _hε'1 lam₁ lam₂ lam₃ h0 hl12 hl23 hl36 hE
  set T : TestFn := tf72T ((6:ℝ)/7) (by norm_num) with hT
  have hanti := TestFn_F_antitone T
  have h16 : lam₁ ≤ 6/7 := le_trans (le_trans hl12 hl23) hl36
  have hb : lam₂ - lam₁ ≤ 6/7 - lam₁ := by linarith
  have hc : lam₃ - lam₁ ≤ 6/7 - lam₁ := by linarith
  have e1 : T.F (6/7 - lam₁) ≤ T.F (lam₂ - lam₁) := hanti hb
  have e2 : T.F (6/7 - lam₁) ≤ T.F (lam₃ - lam₁) := hanti hc
  have hf0 : T.f 0 = 32/35 := by
    rw [hT]; show tf72f (6/7) 0 = 32/35
    rw [tf72f_at_zero (6/7) (by norm_num)]; norm_num
  have hF0 : T.F 0 = 8/9 := by
    rw [hT]; show (tf72Fc (6/7) 0).re = 8/9
    exact tf72Fc_zero_re (6/7) (by norm_num)
  have hF6 : T.F (-(6/7)) = 8/5 := by
    rw [hT]; show (tf72Fc (6/7) ((-(6/7):ℝ) : ℂ)).re = 8/5
    exact tf72Fc_neglam_re (6/7) (by norm_num)
  have hx0 : T.x₀ = 7/3 := by
    rw [hT]; show (2:ℝ)/(6/7) = 7/3; norm_num
  have hf : T.f = tf72f (6/7) := by rw [hT]; rfl
  have hphi : ∀ lam : ℝ, T.F (-lam) - 2 * T.F (6/7 - lam) = tf72fPhi lam := by
    intro lam
    have h := tf72fL_eq_Phi lam
    have hA : T.F (-lam) = ∫ t in (0:ℝ)..(7/3), Real.exp (lam*t) * tf72f (6/7) t := by
      rw [F_eq_tf72f_int T hx0 hf (-lam)]
      apply intervalIntegral.integral_congr
      intro tt _
      dsimp only
      rw [show -((-lam)*tt) = lam*tt from by ring]
    have hB : T.F (6/7 - lam)
        = ∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam)*t)) * tf72f (6/7) t :=
      F_eq_tf72f_int T hx0 hf (6/7 - lam)
    rw [hA, hB]; exact h
  have hphi67 : T.F (-(6/7)) - 2 * T.F 0 = tf72fPhi (6/7) := by
    have h := hphi (6/7)
    rwa [show (6:ℝ)/7 - 6/7 = 0 by ring] at h
  have hElin : T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
      + 16/15 + (256/35) * ε' ≥ 0 := by
    rw [hf0] at hE
    linarith [hE]
  have key : 0 ≤ tf72fPhi lam₁ - tf72fPhi (6/7) + (256/35) * ε' := by
    linarith [hElin, e1, e2, hphi lam₁, hphi67, hF0, hF6]
  have h1 : (104/66825 : ℝ) * (6/7 - lam₁) ≤ (256/35) * ε' := by
    have := tf72fPhi_gap_quant lam₁ h0 h16
    linarith
  have h13 : lam₁ ≤ lam₃ := le_trans hl12 hl23
  have h2 : (104/66825 : ℝ) * (6/7 - lam₃) ≤ (256/35) * ε' := by
    nlinarith [h1, h13]
  have hK : (66825:ℝ) * 256 / (104*35) ≤ 100000 := by norm_num
  have h3 : 6/7 - lam₃ ≤ 100000 * ε' := by
    nlinarith [h2, hε', hK, le_of_lt hε']
  linarith

end Work.OffAxis.Lead
