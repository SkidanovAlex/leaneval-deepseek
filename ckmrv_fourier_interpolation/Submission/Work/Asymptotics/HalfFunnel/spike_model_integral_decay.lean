import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.spike_inv_integral_bound
import Submission.Work.Asymptotics.HalfFunnel.spike_model_integral
import Submission.Work.Asymptotics.HalfFunnel.spike_model_integral_succ

/-!
# Exponential decay of the spike model integral

For `0 < ρ < y`, a natural number `m`, `a > 0` and `0 < |ε| ≤ 1/4` we bound the *signed*
interval integral
`∫_{-ρ}^{ρ} e^{-a(y+u)} (u + iε)⁻¹ u^m du`
by `C · e^{-a(y-ρ)}`, with a constant `C` independent of `a` and `ε`.

The point of the statement is the exponential factor: on `[-ρ,ρ]` we have `y + u ≥ y - ρ`, so
`e^{-a(y+u)} ≤ e^{-a(y-ρ)}`; for `m ≥ 1` the factor `|u|^m/|u+iε| ≤ |u|^{m-1}` is integrable and a
crude estimate already gives the claim.  For `m = 0` the modulus of the integrand is *not*
integrable uniformly in `ε`, so honest cancellation is needed: writing
`(u+iε)⁻¹ = (u - iε)/(u²+ε²)`, the `u`-part is odd and only its symmetrised version survives,
producing a `sinh(a u) u /(u²+ε²)` integrand which is bounded by `a e^{au}`; the `iε`-part is
controlled by `|ε| ∫_{-ρ}^{ρ} (u²+ε²)⁻¹ du ≤ π`.

This refines `spike_model_integral`, which only gives a bound uniform in `a`, to a genuine
exponential decay. -/

set_option linter.unusedVariables false

namespace Work.Asymptotics.HalfFunnel

open MeasureTheory intervalIntegral

/-- `sinh t ≤ t e^t` for every real `t` (used at `t = a u ≥ 0`). -/
lemma spike_sinh_le_mul_exp (t : ℝ) : Real.sinh t ≤ t * Real.exp t := by
  have h2 : Real.exp t * Real.exp (-(2*t)) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  have key : Real.exp t * (1 - Real.exp (-(2*t))) = Real.exp t - Real.exp (-t) := by
    rw [mul_sub, mul_one, h2]
  rw [Real.sinh_eq, ← key]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have h : 1 - Real.exp (-(2*t)) ≤ 2*t := by
    have := Real.one_sub_le_exp_neg (2*t); linarith
  calc Real.exp t * (1 - Real.exp (-(2*t))) ≤ Real.exp t * (2*t) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos t).le
    _ = t * Real.exp t * 2 := by ring

/-- `∫_0^ρ sinh(a u) u/(u²+ε²) du ≤ e^{aρ} - 1` for `a > 0`, `ρ > 0`, `ε ≠ 0`, uniformly in `ε`. -/
lemma spike_integral_sinh_mul_le (a ρ ε : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hε : ε ≠ 0) :
    ∫ u in (0:ℝ)..ρ, Real.sinh (a*u) * u / (u^2 + ε^2) ≤ Real.exp (a*ρ) - 1 := by
  have hε2 : 0 < ε^2 := sq_pos_of_ne_zero hε
  have hden : ∀ u : ℝ, u^2 + ε^2 ≠ 0 := by intro u; nlinarith [sq_nonneg u]
  have hle : (0:ℝ) ≤ ρ := hρ.le
  have hcont_f : Continuous (fun u : ℝ => Real.sinh (a*u) * u / (u^2 + ε^2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · exact hden
  have hcont_g : Continuous (fun u : ℝ => a * Real.exp (a*u)) := by fun_prop
  have hint_f : IntervalIntegrable (fun u : ℝ => Real.sinh (a*u) * u / (u^2 + ε^2)) volume 0 ρ :=
    hcont_f.intervalIntegrable _ _
  have hint_g : IntervalIntegrable (fun u : ℝ => a * Real.exp (a*u)) volume 0 ρ :=
    hcont_g.intervalIntegrable _ _
  have hpt : ∀ u ∈ Set.Icc (0:ℝ) ρ, Real.sinh (a*u) * u / (u^2 + ε^2) ≤ a * Real.exp (a*u) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · subst h; simp; positivity
    · have hd : 0 < u^2 + ε^2 := by nlinarith [sq_nonneg u]
      rw [div_le_iff₀ hd]
      have hKey : Real.sinh (a*u) ≤ a*u*Real.exp (a*u) := by
        have := spike_sinh_le_mul_exp (a*u); linarith
      have h1 : Real.sinh (a*u) * u ≤ (a*u*Real.exp (a*u)) * u :=
        mul_le_mul_of_nonneg_right hKey hu.1
      have h3 : a*Real.exp (a*u)*u^2 ≤ a*Real.exp (a*u)*(u^2+ε^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [sq_nonneg ε]
      calc Real.sinh (a*u) * u ≤ (a*u*Real.exp (a*u)) * u := h1
        _ = a*Real.exp (a*u)*u^2 := by ring
        _ ≤ a*Real.exp (a*u)*(u^2+ε^2) := h3
  have hmono := intervalIntegral.integral_mono_on hle hint_f hint_g hpt
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) ρ,
      HasDerivAt (fun u : ℝ => Real.exp (a*u)) (a * Real.exp (a*x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => a*u) a x := by simpa using (hasDerivAt_id x).const_mul a
    simpa [mul_comm] using h1.exp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_g
  rw [hftc] at hmono
  simpa using hmono

/-- For an even function, `∫_{-ρ}^{ρ} h = 2 ∫_0^ρ h`. -/
lemma spike_intervalIntegral_even {ρ : ℝ} {h : ℝ → ℝ} (heven : ∀ x, h (-x) = h x)
    (hint : IntervalIntegrable h volume (-ρ) 0) (hint2 : IntervalIntegrable h volume 0 ρ) :
    ∫ x in (-ρ)..ρ, h x = 2 * ∫ x in 0..ρ, h x := by
  have hcomp := intervalIntegral.integral_comp_neg (f := h) (a := (0:ℝ)) (b := ρ)
  have hL : ∫ x in (0:ℝ)..ρ, h (-x) = ∫ x in 0..ρ, h x := by
    apply intervalIntegral.integral_congr; intro x _; exact heven x
  rw [hL] at hcomp
  simp only [neg_zero] at hcomp
  have hadj := intervalIntegral.integral_add_adjacent_intervals hint hint2
  rw [← hcomp] at hadj
  linarith

/-- **The numerator (odd) part.**  For `0 < ρ < y`, `a > 0`, `ε ≠ 0`,
`|∫_{-ρ}^{ρ} e^{-a(y+u)} u/(u²+ε²) du| ≤ 2 e^{-a(y-ρ)}`.

Symmetrising `u ↦ -u` turns the (odd) integrand into `-2 e^{-a y} sinh(a u) u/(u²+ε²)` whose
absolute value is bounded by `a e^{a|u|}`; integrating gives `2(e^{aρ}-1)`. -/
lemma spike_re_num_integral_bound {a y ρ ε : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρy : ρ < y) (hε : ε ≠ 0) :
    |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u))) * u / (u^2 + ε^2)| ≤ 2 * Real.exp (-(a*(y-ρ))) := by
  have hε2 : 0 < ε^2 := sq_pos_of_ne_zero hε
  have hdpos : ∀ u : ℝ, 0 < u^2 + ε^2 := by intro u; nlinarith [sq_nonneg u]
  have hden : ∀ u : ℝ, u^2 + ε^2 ≠ 0 := fun u => (hdpos u).ne'
  set φ : ℝ → ℝ := fun u => Real.exp (-(a*(y+u))) * u / (u^2 + ε^2) with hφdef
  set hh : ℝ → ℝ := fun u => Real.sinh (a*u) * u / (u^2 + ε^2) with hhdef
  have hcontφ : Continuous φ := by
    rw [hφdef]; apply Continuous.div
    · fun_prop
    · fun_prop
    · exact hden
  have hconth : Continuous hh := by
    rw [hhdef]; apply Continuous.div
    · fun_prop
    · fun_prop
    · exact hden
  have hintφ : IntervalIntegrable φ volume (-ρ) ρ := hcontφ.intervalIntegrable _ _
  have hintφneg : IntervalIntegrable (fun x => φ (-x)) volume (-ρ) ρ :=
    (hcontφ.comp continuous_neg).intervalIntegrable _ _
  have hcomp : ∫ x in (-ρ)..ρ, φ (-x) = ∫ x in (-ρ)..ρ, φ x := by
    simpa using intervalIntegral.integral_comp_neg (f := φ) (a := (-ρ)) (b := ρ)
  have hsum : ∫ x in (-ρ)..ρ, (φ x + φ (-x)) = 2 * ∫ x in (-ρ)..ρ, φ x := by
    rw [intervalIntegral.integral_add hintφ hintφneg, hcomp]; ring
  have hpt : ∀ x, φ x + φ (-x) = -2 * Real.exp (-(a*y)) * hh x := by
    intro x
    simp only [hφdef, hhdef]
    have hxx : (-x)^2 = x^2 := by ring
    rw [hxx]
    have hxx2 : y + -x = y - x := by ring
    rw [hxx2]
    have key : Real.exp (-(a*(y+x))) - Real.exp (-(a*(y-x)))
        = -2*Real.exp (-(a*y))*Real.sinh (a*x) := by
      rw [Real.sinh_eq]
      rw [show -(a*(y+x)) = -(a*y) + (-(a*x)) by ring,
          show -(a*(y-x)) = -(a*y) + (a*x) by ring]
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [show Real.exp (-(a*(y+x)))*x/(x^2+ε^2) + Real.exp (-(a*(y-x)))*(-x)/(x^2+ε^2)
          = (Real.exp (-(a*(y+x))) - Real.exp (-(a*(y-x))))*x/(x^2+ε^2) by ring]
    rw [key]; ring
  have hhnonneg : ∀ x, 0 ≤ hh x := by
    intro x
    simp only [hhdef]
    apply div_nonneg _ (hdpos x).le
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg ha.le hx)) hx
    · exact mul_nonneg_of_nonpos_of_nonpos
        (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le hx)) hx
  have habs : ∀ x, |φ x + φ (-x)| = 2 * Real.exp (-(a*y)) * hh x := by
    intro x
    rw [hpt x]
    have hE : (0:ℝ) < Real.exp (-(a*y)) := Real.exp_pos _
    rw [show -2 * Real.exp (-(a*y)) * hh x = (-(2 * Real.exp (-(a*y)))) * hh x by ring]
    rw [abs_mul, abs_of_neg (by linarith), abs_of_nonneg (hhnonneg x)]
    ring
  have hin0 : IntervalIntegrable hh volume (-ρ) 0 := hconth.intervalIntegrable _ _
  have hin1 : IntervalIntegrable hh volume 0 ρ := hconth.intervalIntegrable _ _
  have hheven : ∀ x, hh (-x) = hh x := by
    intro x
    simp only [hhdef]
    rw [show a*(-x) = -(a*x) by ring, Real.sinh_neg]
    ring
  have hH2 : ∫ u in (0:ℝ)..ρ, hh u ≤ Real.exp (a*ρ) - 1 := by
    rw [hhdef]; exact spike_integral_sinh_mul_le a ρ ε ha hρ hε
  have heven_int : ∫ x in (-ρ)..ρ, hh x = 2 * ∫ x in 0..ρ, hh x :=
    spike_intervalIntegral_even hheven hin0 hin1
  have hIntge : ∫ x in (-ρ)..ρ, |φ x + φ (-x)| = 2 * Real.exp (-(a*y)) * ∫ x in (-ρ)..ρ, hh x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    exact habs x
  have habsint := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun x => φ x + φ (-x)) (a := -ρ) (b := ρ) (by linarith)
  rw [hsum] at habsint
  have hmain : 2 * |∫ x in (-ρ)..ρ, φ x| ≤ 4 * Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1) := by
    rw [abs_mul] at habsint
    norm_num at habsint
    rw [hIntge] at habsint
    have hbound : ∫ x in (-ρ)..ρ, hh x ≤ 2 * (Real.exp (a*ρ) - 1) := by
      rw [heven_int]; linarith [hH2]
    nlinarith [Real.exp_pos (-(a*y)), hbound, habsint]
  have hfin : |∫ x in (-ρ)..ρ, φ x| ≤ 2 * Real.exp (-(a*(y-ρ))) := by
    have hE : 0 < Real.exp (-(a*y)) := Real.exp_pos _
    have hexp_le : Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1) ≤ Real.exp (-(a*(y-ρ))) := by
      have h1 : Real.exp (a*ρ) - 1 ≤ Real.exp (a*ρ) := by linarith [Real.exp_pos (a*ρ)]
      calc Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1) ≤ Real.exp (-(a*y)) * Real.exp (a*ρ) :=
            mul_le_mul_of_nonneg_left h1 hE.le
        _ = Real.exp (-(a*(y-ρ))) := by rw [← Real.exp_add]; congr 1; ring
    have h4 : 4 * Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1) ≤ 4 * Real.exp (-(a*(y-ρ))) := by
      have hh4 : (4:ℝ) * (Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1))
          ≤ 4 * Real.exp (-(a*(y-ρ))) :=
        mul_le_mul_of_nonneg_left hexp_le (by norm_num)
      calc 4 * Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1)
          = 4 * (Real.exp (-(a*y)) * (Real.exp (a*ρ) - 1)) := by ring
        _ ≤ 4 * Real.exp (-(a*(y-ρ))) := hh4
    linarith
  exact hfin

/-- **The denominator (polar) part.**  For `0 < ρ < y`, `a > 0`, `ε ≠ 0`,
`∫_{-ρ}^{ρ} e^{-a(y+u)}/(u²+ε²) du ≤ e^{-a(y-ρ)} · π/|ε|`. -/
lemma spike_re_den_integral_bound {a y ρ ε : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρy : ρ < y) (hε : ε ≠ 0) :
    ∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u))) / (u^2 + ε^2)
      ≤ Real.exp (-(a*(y-ρ))) * (Real.pi / |ε|) := by
  have hεpos : 0 < |ε| := abs_pos.mpr hε
  have hle : -ρ ≤ ρ := by linarith
  have hdpos : ∀ u : ℝ, 0 < u^2 + ε^2 := by intro u; nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
  have hden : ∀ u : ℝ, u^2 + ε^2 ≠ 0 := fun u => (hdpos u).ne'
  have hcont1 : Continuous (fun u : ℝ => Real.exp (-(a*(y+u))) / (u^2+ε^2)) :=
    Continuous.div (by fun_prop) (by fun_prop) hden
  have hcont2 : Continuous (fun u : ℝ => Real.exp (-(a*(y-ρ))) * (u^2+ε^2)⁻¹) := by
    apply Continuous.mul (by fun_prop)
    exact Continuous.inv₀ (by fun_prop) hden
  have hmono : ∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2)
      ≤ ∫ u in (-ρ)..ρ, Real.exp (-(a*(y-ρ)))*(u^2+ε^2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hle (hcont1.intervalIntegrable (-ρ) ρ)
      (hcont2.intervalIntegrable (-ρ) ρ)
    intro u hu
    have hD : 0 < u^2+ε^2 := hdpos u
    have hexp : Real.exp (-(a*(y+u))) ≤ Real.exp (-(a*(y-ρ))) := by
      apply Real.exp_le_exp.mpr; nlinarith [hu.1, ha.le]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr hD.le)
  calc ∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2)
      ≤ ∫ u in (-ρ)..ρ, Real.exp (-(a*(y-ρ)))*(u^2+ε^2)⁻¹ := hmono
    _ = Real.exp (-(a*(y-ρ))) * ∫ u in (-ρ)..ρ, (u^2+ε^2)⁻¹ := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp (-(a*(y-ρ))) * (Real.pi/|ε|) :=
          mul_le_mul_of_nonneg_left (spike_inv_sq_integral_le hε) (Real.exp_nonneg _)

/-- The base case `m = 0`: `‖∫_{-ρ}^{ρ} e^{-a(y+u)}(u+iε)⁻¹ du‖ ≤ (π+2) e^{-a(y-ρ)}`. -/
theorem spike_model_integral_decay_zero {y ρ : ℝ} (hy : 0 < y) (hρ : 0 < ρ) (hρy : ρ < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖
        ≤ C * Real.exp (-(a*(y-ρ))) := by
  refine ⟨Real.pi + 2, by positivity, ?_⟩
  intro a ε ha hε hε4
  have hdpos : ∀ u : ℝ, 0 < u^2+ε^2 := by intro u; nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
  have hden : ∀ u : ℝ, u^2+ε^2 ≠ 0 := fun u => (hdpos u).ne'
  have hp := spike_re_num_integral_bound (a:=a) (y:=y) (ρ:=ρ) (ε:=ε) ha hρ hρy hε
  have hq := spike_re_den_integral_bound (a:=a) (y:=y) (ρ:=ρ) (ε:=ε) ha hρ hρy hε
  have hpt : ∀ u : ℝ, Complex.exp (-(a:ℂ)*((y:ℂ)+(u:ℂ))) * ((u:ℂ)+(ε:ℂ)*Complex.I)⁻¹
      = ((Real.exp (-(a*(y+u)))*u/(u^2+ε^2) : ℝ):ℂ)
        - ((ε:ℂ)*Complex.I)*((Real.exp (-(a*(y+u)))/(u^2+ε^2) : ℝ):ℂ) := by
    intro u
    rw [spike_exp_neg_mul_ofReal, spike_inv_add_mul_I hε]
    have hD : ((u^2+ε^2:ℝ):ℂ) ≠ 0 := by exact_mod_cast hden u
    push_cast
    field_simp
  have hcongr : ∫ u in (-ρ)..ρ, Complex.exp (-(a:ℂ)*((y:ℂ)+(u:ℂ))) * ((u:ℂ)+(ε:ℂ)*Complex.I)⁻¹
      = ∫ u in (-ρ)..ρ, (((Real.exp (-(a*(y+u)))*u/(u^2+ε^2) : ℝ):ℂ)
          - ((ε:ℂ)*Complex.I)*((Real.exp (-(a*(y+u)))/(u^2+ε^2) : ℝ):ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact hpt u
  have hcontp : Continuous (fun u : ℝ => ((Real.exp (-(a*(y+u)))*u/(u^2+ε^2) : ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (Continuous.div (by fun_prop) (by fun_prop) hden)
  have hcontq : Continuous
      (fun u : ℝ => ((ε:ℂ)*Complex.I)*((Real.exp (-(a*(y+u)))/(u^2+ε^2) : ℝ):ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp
      (Continuous.div (by fun_prop) (by fun_prop) hden))
  rw [hcongr, intervalIntegral.integral_sub (hcontp.intervalIntegrable (-ρ) ρ)
      (hcontq.intervalIntegrable (-ρ) ρ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  have hq0 : 0 ≤ ∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2) :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => div_nonneg (Real.exp_nonneg _) (hdpos u).le)
  have hAB : ‖((∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))*u/(u^2+ε^2) : ℝ):ℂ)
        - ((ε:ℂ)*Complex.I)*((∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2) : ℝ):ℂ)‖
      ≤ |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))*u/(u^2+ε^2)|
        + |ε| * |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2)| := by
    calc _ ≤ ‖((∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))*u/(u^2+ε^2) : ℝ):ℂ)‖
            + ‖((ε:ℂ)*Complex.I)*((∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2) : ℝ):ℂ)‖ :=
          norm_sub_le _ _
      _ = |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))*u/(u^2+ε^2)|
            + |ε| * |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2)| := by
          rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              Real.norm_eq_abs]
  calc _ ≤ |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))*u/(u^2+ε^2)|
            + |ε| * |∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2)| := hAB
    _ ≤ 2 * Real.exp (-(a*(y-ρ))) + Real.pi * Real.exp (-(a*(y-ρ))) := by
        apply add_le_add hp ?_
        rw [abs_of_nonneg hq0]
        calc |ε| * ∫ u in (-ρ)..ρ, Real.exp (-(a*(y+u)))/(u^2+ε^2)
            ≤ |ε| * (Real.exp (-(a*(y-ρ))) * (Real.pi/|ε|)) :=
              mul_le_mul_of_nonneg_left hq (abs_nonneg ε)
          _ = Real.pi * Real.exp (-(a*(y-ρ))) := by
                have hne : (|ε|:ℝ) ≠ 0 := abs_ne_zero.mpr hε
                field_simp
    _ = (Real.pi + 2) * Real.exp (-(a*(y-ρ))) := by ring

/-- The case `m ≥ 1`: the factor `|u|^m/|u+iε| ≤ |u|^{m-1} ≤ ρ^{m-1}` is integrable, giving
`‖∫_{-ρ}^{ρ} e^{-a(y+u)}(u+iε)⁻¹ u^m du‖ ≤ 2ρ^m e^{-a(y-ρ)}`. -/
theorem spike_model_integral_decay_pos (m : ℕ) (hm : 1 ≤ m) {y ρ : ℝ} (hy : 0 < y) (hρ : 0 < ρ)
    (hρy : ρ < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1/4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a:ℂ)*((y:ℂ)+(u:ℂ))) * ((u:ℂ)+(ε:ℂ)*Complex.I)⁻¹ * ((u:ℂ)^m)‖
        ≤ C * Real.exp (-(a*(y-ρ))) := by
  refine ⟨2 * ρ^m, by positivity, ?_⟩
  intro a ε ha hε hε4
  have hle : -ρ ≤ ρ := by linarith
  have hpow : ∀ (t : ℝ), t^m = t^(m-1) * t := by
    intro t
    conv_lhs => rw [show m = (m-1)+1 from (Nat.sub_add_cancel hm).symm]
    rw [pow_succ]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -ρ) (b := ρ)
    (C := Real.exp (-(a*(y-ρ))) * ρ^(m-1))
    (f := fun u : ℝ => Complex.exp (-(a:ℂ)*((y:ℂ)+(u:ℂ))) * ((u:ℂ)+(ε:ℂ)*Complex.I)⁻¹
      * ((u:ℂ)^m)) ?_
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ - -ρ)] at h
    calc _ ≤ Real.exp (-(a*(y-ρ))) * ρ^(m-1) * (ρ - -ρ) := h
      _ = 2 * ρ^m * Real.exp (-(a*(y-ρ))) := by rw [hpow ρ]; ring
  · intro u hu
    rw [Set.uIoc_of_le hle] at hu
    have huI : -ρ ≤ u ∧ u ≤ ρ := ⟨le_of_lt hu.1, hu.2⟩
    have huabs : |u| ≤ ρ := abs_le.mpr huI
    have hsq : ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖^2 = u^2+ε^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hge : |u| ≤ ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖ := by
      nlinarith [sq_abs u, hsq, sq_nonneg ε, norm_nonneg ((u:ℂ)+(ε:ℂ)*Complex.I), abs_nonneg u]
    have hcpos : 0 < ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖ := by
      have h2 : 0 < ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖^2 := by
        rw [hsq]; nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
      nlinarith [norm_nonneg ((u:ℂ)+(ε:ℂ)*Complex.I)]
    have hEnorm : ‖Complex.exp (-(a:ℂ)*((y:ℂ)+(u:ℂ)))‖ = Real.exp (-(a*(y+u))) := by
      rw [Complex.norm_exp]; simp
    have hnormpow : ‖(u:ℂ)^m‖ = |u|^m := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, hEnorm, hnormpow, norm_inv]
    have hexp : Real.exp (-(a*(y+u))) ≤ Real.exp (-(a*(y-ρ))) := by
      apply Real.exp_le_exp.mpr; nlinarith [huI.1, ha.le]
    have hpa : |u|^(m-1) ≤ ρ^(m-1) := pow_le_pow_left₀ (abs_nonneg u) huabs (m-1)
    have hc : |u| * ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hcpos]
      exact hge
    have hinner : |u|^m * ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖⁻¹ ≤ ρ^(m-1) := by
      have hkey : |u|^(m-1) * (|u| * ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖⁻¹) ≤ ρ^(m-1) * 1 :=
        mul_le_mul hpa hc (by positivity) (by positivity)
      rw [mul_one] at hkey
      rw [hpow |u|, mul_assoc]
      exact hkey
    calc Real.exp (-(a*(y+u))) * ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖⁻¹ * |u|^m
        = Real.exp (-(a*(y+u))) * (|u|^m * ‖((u:ℂ)+(ε:ℂ)*Complex.I)‖⁻¹) := by ring
      _ ≤ Real.exp (-(a*(y-ρ))) * ρ^(m-1) :=
          mul_le_mul hexp hinner (by positivity) (by positivity)

theorem spike_model_integral_decay (m : ℕ) {y ρ : ℝ} (hy : 0 < y) (hρ : 0 < ρ) (hρy : ρ < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m)‖
        ≤ C * Real.exp (-(a * (y - ρ))) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C, hC, h⟩ := spike_model_integral_decay_zero hy hρ hρy
    exact ⟨C, hC, fun a ε ha hε hε4 => by simpa using h a ε ha hε hε4⟩
  · exact spike_model_integral_decay_pos m hm hy hρ hρy

end Work.Asymptotics.HalfFunnel
