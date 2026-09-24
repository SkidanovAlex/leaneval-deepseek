import Mathlib
import Submission.Work.GM.S2.osc_integral_bound
import Submission.Work.GM.S2.vdc_imports

/-!
# The sharp `(1+|σ|)^{-1/2}` bound for `∫_V^W v^{iσ-1} e(-v) dv`

Guth–Maynard §6 needs, for `[V,W] ⊆ [1,∞)` and every real `σ`, the estimate
`‖∫_V^W v^{iσ-1} e(-v) dv‖ ≤ C (1+|σ|)^{-1/2}`, uniformly in `V ≤ W`.
This strengthens `osc_integral_bound` (`[V,2V]` with the weaker `V/√(1+|σ|)`).

Substituting `v = e^s` turns the integral into the pure phase integral
`∫_{log V}^{log W} exp(i φ(s)) ds` with `φ(s) = σ s - 2π e^s`, `φ' = σ - 2π e^s`,
`φ'' = -2π e^s`.  Writing `X := 2π e^{log V} = 2πV`:

* `|σ| ≤ X`: `|φ''| ≥ 2π e^s ≥ X` on the whole interval, so the second-derivative
  van der Corput bound gives `≤ 1000/√X ≤ 1000√2/√(1+|σ|)` (as `X ≥ 1`).
* `σ < -X`: `φ'(s) = σ - 2πe^s ≤ σ < 0` and `|φ'| = 2πe^s - σ ≥ |σ|`, so the
  first-derivative bound gives `≤ 4/|σ| ≤ 4√2/√(1+|σ|)` (as `|σ| ≥ X ≥ 1`).
* `σ > X`: then `e^{log V} < σ/(2π)`.  On the set where `e^s ≤ σ/(4π)` we have
  `φ' ≥ σ/2`, and on the set where `e^s ≥ σ/(4π)` we have `|φ''| = 2πe^s ≥ σ/2`.
  Splitting `[log V, log W]` at the (possibly degenerate) point `log(σ/(4π))`
  therefore gives `≤ 8/σ + 1000/√(σ/2) ≤ C/√(1+σ)` (as `σ ≥ 2π ≥ 1`).
-/

open MeasureTheory Set
open scoped Real Interval ComplexConjugate

set_option autoImplicit false

namespace Work.GM.S2

noncomputable section

open Commons.Analysis.Oscillatory

/-! ## Elementary facts about the phase `phase σ s = σ s - 2π e^s` -/

lemma hasDerivAt_phase (σ s : ℝ) :
    HasDerivAt (phase σ) (σ - 2 * Real.pi * Real.exp s) s := by
  have h1 : HasDerivAt (fun s : ℝ => σ * s) σ s := by
    simpa using (hasDerivAt_id s).const_mul σ
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.pi * Real.exp s) (2 * Real.pi * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul (2 * Real.pi)
  exact (h1.sub h2)

lemma deriv_phase (σ : ℝ) : deriv (phase σ) = fun s => σ - 2 * Real.pi * Real.exp s := by
  funext s
  exact (hasDerivAt_phase σ s).deriv

lemma contDiff_phase (σ : ℝ) : ContDiff ℝ 2 (phase σ) := by
  unfold phase; fun_prop

lemma iteratedDeriv_two_phase (σ : ℝ) :
    iteratedDeriv 2 (phase σ) = fun s => -(2 * Real.pi * Real.exp s) := by
  have h2eq : iteratedDeriv 2 (phase σ) = deriv (deriv (phase σ)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2eq, deriv_phase]
  funext s
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.pi * Real.exp s) (2 * Real.pi * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul (2 * Real.pi)
  exact (h2.const_sub σ).deriv

lemma antitoneOn_deriv_phase (σ a b : ℝ) :
    AntitoneOn (deriv (phase σ)) (Set.Icc a b) := by
  rw [deriv_phase]
  intro x _ y _ hxy
  have h := Real.exp_le_exp.mpr hxy
  nlinarith [h, Real.pi_pos]

/-! ## van der Corput bounds specialized to the phase -/

/-- First-derivative (van der Corput) bound for the phase `phase σ`. -/
lemma vdc_first_deriv_phase {a b σ lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hbound : ∀ x ∈ Set.Icc a b, lam ≤ |deriv (phase σ) x|) :
    ‖∫ t in a..b, osc (phase σ) t‖ ≤ 4 / lam :=
  Commons.Analysis.Oscillatory.vdc_first_deriv hab hlam (contDiff_phase σ)
    (Or.inr (antitoneOn_deriv_phase σ a b)) hbound

/-- Second-derivative (van der Corput) bound for the phase `phase σ`, with the
explicit constant `1000`.  Since `iteratedDeriv 2 (phase σ) = -2π e^s < 0` we can
apply the positive-curvature version to `-phase σ` and use conjugation. -/
lemma vdc_two_phase {a b σ lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hbound : ∀ t ∈ Set.Ioo a b, lam ≤ |iteratedDeriv 2 (phase σ) t|) :
    ‖∫ t in a..b, osc (phase σ) t‖ ≤ 1000 / lam ^ ((1:ℝ)/2) := by
  have hψc : ContDiffOn ℝ 2 (fun t => -phase σ t) (Set.Icc a b) :=
    (contDiff_phase σ).neg.contDiffOn
  have h2 : ∀ t ∈ Set.Ioo a b, lam ≤ iteratedDeriv 2 (fun t => -phase σ t) t := by
    intro t ht
    have h := hbound t ht
    rw [iteratedDeriv_two_phase, abs_neg, abs_of_nonneg (by positivity)] at h
    rw [iteratedDeriv_fun_neg, iteratedDeriv_two_phase]
    linarith
  have hb := Commons.Analysis.Oscillatory.vdc_two_pos hab hlam hψc h2
  have hconj : (∫ t in a..b, osc (fun t => -phase σ t) t)
      = conj (∫ t in a..b, osc (phase σ) t) := by
    rw [show (fun t => osc (fun t => -phase σ t) t)
          = (fun t => conj (osc (phase σ) t)) from
        funext (fun t => Commons.Analysis.Oscillatory.osc_neg_conj (phase σ) t),
      intervalIntegral.intervalIntegral_conj]
  rwa [hconj, Complex.norm_conj] at hb

/-! ## Numeric conversions -/

lemma rpow_neg_half_eq (x : ℝ) (hx : 0 < x) : x ^ (-(1/2:ℝ)) = 1 / Real.sqrt x := by
  rw [Real.rpow_neg (le_of_lt hx), ← Real.sqrt_eq_rpow, one_div]

/-- Case `|σ| ≤ X` with `X ≥ 1`: `1000/√X ≤ C(1+|σ|)^{-1/2}`. -/
lemma conv_A {σ X : ℝ} (hX1 : 1 ≤ X) (hσX : |σ| ≤ X) :
    1000 / Real.sqrt X ≤ 10000 * (1 + |σ|) ^ (-(1/2:ℝ)) := by
  rw [rpow_neg_half_eq (1 + |σ|) (by positivity), mul_one_div]
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by positivity))]
  have h1 : Real.sqrt (1 + |σ|) ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
  have h3 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h4 : (0:ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  nlinarith [h1, h2, h3, h4]

/-- Case `|σ| ≥ 1`: `4/|σ| ≤ C(1+|σ|)^{-1/2}`. -/
lemma conv_N {σ : ℝ} (hσ : 1 ≤ |σ|) :
    4 / |σ| ≤ 10000 * (1 + |σ|) ^ (-(1/2:ℝ)) := by
  rw [rpow_neg_half_eq (1 + |σ|) (by positivity), mul_one_div]
  rw [div_le_div_iff₀ (by linarith) (Real.sqrt_pos.mpr (by positivity))]
  have hs : Real.sqrt (1 + |σ|) ≤ 2 * |σ| := by
    have h2 : (1 + |σ|) ≤ (2 * |σ|)^2 := by nlinarith [abs_nonneg σ, hσ]
    calc Real.sqrt (1 + |σ|) ≤ Real.sqrt ((2 * |σ|)^2) := Real.sqrt_le_sqrt h2
      _ = 2 * |σ| := Real.sqrt_sq (by positivity)
  nlinarith [hs]

/-- Case `σ ≥ 1`: `8/σ + 1000/√(σ/2) ≤ C(1+σ)^{-1/2}`. -/
lemma conv_B {σ : ℝ} (hσ : 1 ≤ σ) :
    8 / σ + 1000 / Real.sqrt (σ / 2) ≤ 10000 * (1 + σ) ^ (-(1/2:ℝ)) := by
  have hσpos : (0:ℝ) < σ := by linarith
  have hspos : 0 < Real.sqrt (1 + σ) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (1 + σ) ≤ 2 * σ := by
    have h2 : (1 + σ) ≤ (2 * σ)^2 := by nlinarith
    calc Real.sqrt (1 + σ) ≤ Real.sqrt ((2*σ)^2) := Real.sqrt_le_sqrt h2
      _ = 2 * σ := Real.sqrt_sq (by positivity)
  have h1 : 8 / σ ≤ 3000 / Real.sqrt (1 + σ) := by
    rw [div_le_div_iff₀ hσpos hspos]; nlinarith [hsq]
  have h2 : 1000 / Real.sqrt (σ / 2) ≤ 3000 / Real.sqrt (1 + σ) := by
    have hsig : 0 < Real.sqrt (σ/2) := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_div_iff₀ hsig hspos]
    have hs : Real.sqrt (1 + σ) ≤ 3 * Real.sqrt (σ/2) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hexp : (3 * Real.sqrt (σ/2))^2 = 9 * (σ/2) := by
        rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ σ/2)]
        ring
      rw [hexp]; linarith
    nlinarith [hs]
  rw [rpow_neg_half_eq (1 + σ) (by linarith), mul_one_div]
  calc 8 / σ + 1000 / Real.sqrt (σ / 2)
      ≤ 3000 / Real.sqrt (1+σ) + 3000 / Real.sqrt (1+σ) := by linarith
    _ = 6000 / Real.sqrt (1+σ) := by ring
    _ ≤ 10000 / Real.sqrt (1+σ) := by
        rw [div_le_div_iff₀ hspos hspos]; nlinarith [Real.sqrt_nonneg (1+σ)]

/-! ## The two elementary phase estimates in the region `e^s ≤ σ/(4π)` / `σ/(4π) ≤ e^s` -/

lemma two_pi_mul_div_four_pi {σ : ℝ} (hσ : 0 < σ) :
    2 * Real.pi * (σ / (4 * Real.pi)) = σ / 2 := by
  field_simp
  ring

lemma exp_le_of_le_log {σ s : ℝ} (hσ : 0 < σ) (h : s ≤ Real.log (σ / (4 * Real.pi))) :
    Real.exp s ≤ σ / (4 * Real.pi) := by
  have h1 : Real.exp s ≤ Real.exp (Real.log (σ / (4 * Real.pi))) := Real.exp_le_exp.mpr h
  rwa [Real.exp_log (by positivity)] at h1

lemma le_exp_of_log_le {σ s : ℝ} (hσ : 0 < σ) (h : Real.log (σ / (4 * Real.pi)) ≤ s) :
    σ / (4 * Real.pi) ≤ Real.exp s := by
  have h1 : Real.exp (Real.log (σ / (4 * Real.pi))) ≤ Real.exp s := Real.exp_le_exp.mpr h
  rwa [Real.exp_log (by positivity)] at h1

lemma deriv_phase_ge_half {σ s : ℝ} (hσ : 0 < σ)
    (h : Real.exp s ≤ σ / (4 * Real.pi)) : σ / 2 ≤ deriv (phase σ) s := by
  rw [deriv_phase]
  have h4 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  rw [two_pi_mul_div_four_pi hσ] at h4
  linarith

lemma abs_deriv_phase_ge_half {σ s : ℝ} (hσ : 0 < σ)
    (h : Real.exp s ≤ σ / (4 * Real.pi)) : σ / 2 ≤ |deriv (phase σ) s| := by
  have h1 := deriv_phase_ge_half hσ h
  rw [abs_of_nonneg (by linarith)]
  exact h1

lemma abs_iteratedDeriv_two_phase_ge_half {σ s : ℝ} (hσ : 0 < σ)
    (h : σ / (4 * Real.pi) ≤ Real.exp s) : σ / 2 ≤ |iteratedDeriv 2 (phase σ) s| := by
  have h4 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  rw [two_pi_mul_div_four_pi hσ] at h4
  rw [iteratedDeriv_two_phase, abs_neg, abs_of_nonneg (by positivity)]
  linarith

/-! ## The phase integral bound -/

/-- The pure phase integral bound: `‖∫_a^b exp(i(σs - 2π e^s)) ds‖ ≤ C(1+|σ|)^{-1/2}`
for `0 ≤ a ≤ b`. -/
lemma phase_integral_bound_aux (a b σ : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖∫ t in a..b, osc (phase σ) t‖ ≤ 10000 * (1 + |σ|) ^ (-(1/2:ℝ)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexpa : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hX1 : 1 ≤ 2 * Real.pi * Real.exp a := by nlinarith [hexpa, hpi, Real.pi_gt_three]
  have hXpos : 0 < 2 * Real.pi * Real.exp a := by linarith
  by_cases hA : |σ| ≤ 2 * Real.pi * Real.exp a
  · -- Case A: `|σ| ≤ 2π e^a`
    have hbnd : ∀ t ∈ Set.Ioo a b, 2 * Real.pi * Real.exp a ≤ |iteratedDeriv 2 (phase σ) t| := by
      intro t ht
      have he : Real.exp a ≤ Real.exp t := Real.exp_le_exp.mpr (le_of_lt ht.1)
      have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      rw [iteratedDeriv_two_phase, abs_neg, abs_of_nonneg (by positivity)]
      linarith
    refine (vdc_two_phase hab hXpos hbnd).trans ?_
    rw [← Real.sqrt_eq_rpow]
    exact conv_A hX1 hA
  · have hlt : 2 * Real.pi * Real.exp a < |σ| := not_le.mp hA
    rcases lt_abs.mp hlt with hB | hC
    · -- Case B: `σ > 2π e^a`
      have hσpos : 0 < σ := by linarith
      have hσ1 : 1 ≤ σ := by linarith
      by_cases hb1 : b ≤ Real.log (σ / (4 * Real.pi))
      · -- B.1: the whole interval lies in `e^s ≤ σ/(4π)`
        have hbnd : ∀ x ∈ Set.Icc a b, σ / 2 ≤ |deriv (phase σ) x| := by
          intro x hx
          exact abs_deriv_phase_ge_half hσpos
            (exp_le_of_le_log hσpos (le_trans hx.2 hb1))
        have h8 : ‖∫ t in a..b, osc (phase σ) t‖ ≤ 8 / σ := by
          have h := vdc_first_deriv_phase hab (by linarith : 0 < σ/2) hbnd
          have heq : 4 / (σ/2) = 8 / σ := by ring
          rwa [heq] at h
        rw [abs_of_pos hσpos]
        have hp2 : (0:ℝ) ≤ 1000 / Real.sqrt (σ / 2) := by positivity
        linarith [conv_B hσ1, hp2, h8]
      · rw [not_le] at hb1
        by_cases ha1 : Real.log (σ / (4 * Real.pi)) ≤ a
        · -- B.2.i: the whole interval lies in `σ/(4π) ≤ e^s`
          have hbnd : ∀ t ∈ Set.Ioo a b, σ / 2 ≤ |iteratedDeriv 2 (phase σ) t| := by
            intro t ht
            exact abs_iteratedDeriv_two_phase_ge_half hσpos
              (le_exp_of_log_le hσpos (le_trans ha1 (le_of_lt ht.1)))
          refine (vdc_two_phase hab (by linarith : 0 < σ/2) hbnd).trans ?_
          rw [← Real.sqrt_eq_rpow, abs_of_pos hσpos]
          have hp1 : (0:ℝ) ≤ 8 / σ := by positivity
          linarith [conv_B hσ1, hp1]
        · rw [not_le] at ha1
          -- B.2.ii: split at `v = log(σ/(4π)) ∈ (a,b)`
          have hpiece1 : ‖∫ t in a..(Real.log (σ/(4*Real.pi))), osc (phase σ) t‖ ≤ 8 / σ := by
            have hbnd : ∀ x ∈ Set.Icc a (Real.log (σ / (4*Real.pi))),
                σ / 2 ≤ |deriv (phase σ) x| := by
              intro x hx
              exact abs_deriv_phase_ge_half hσpos (exp_le_of_le_log hσpos hx.2)
            have h := vdc_first_deriv_phase (le_of_lt ha1) (by linarith : 0 < σ/2) hbnd
            have heq : 4 / (σ/2) = 8 / σ := by ring
            rwa [heq] at h
          have hpiece2 : ‖∫ t in (Real.log (σ/(4*Real.pi)))..b, osc (phase σ) t‖ ≤
              1000 / Real.sqrt (σ / 2) := by
            have hbnd : ∀ t ∈ Set.Ioo (Real.log (σ/(4*Real.pi))) b,
                σ / 2 ≤ |iteratedDeriv 2 (phase σ) t| := by
              intro t ht
              exact abs_iteratedDeriv_two_phase_ge_half hσpos
                (le_exp_of_log_le hσpos (le_of_lt ht.1))
            have h := vdc_two_phase (le_of_lt hb1) (by linarith : 0 < σ/2) hbnd
            rwa [← Real.sqrt_eq_rpow] at h
          have hcont : Continuous (osc (phase σ)) := by
            have h1 : Continuous fun t : ℝ => Complex.I * ((phase σ t : ℝ) : ℂ) :=
              continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_phase σ).continuous)
            exact Complex.continuous_exp.comp h1
          have hInt1 : IntervalIntegrable (osc (phase σ)) volume a (Real.log (σ/(4*Real.pi))) :=
            hcont.intervalIntegrable a _
          have hInt2 : IntervalIntegrable (osc (phase σ)) volume (Real.log (σ/(4*Real.pi))) b :=
            hcont.intervalIntegrable _ b
          have hsplit := intervalIntegral.integral_add_adjacent_intervals
            (f := osc (phase σ)) hInt1 hInt2
          have hsplit2 : ∫ t in a..b, osc (phase σ) t
              = (∫ t in a..(Real.log (σ/(4*Real.pi))), osc (phase σ) t)
                + (∫ t in (Real.log (σ/(4*Real.pi)))..b, osc (phase σ) t) := by
            rw [← hsplit]
          have hstep : ‖∫ t in a..b, osc (phase σ) t‖
              ≤ ‖∫ t in a..(Real.log (σ/(4*Real.pi))), osc (phase σ) t‖
                + ‖∫ t in (Real.log (σ/(4*Real.pi)))..b, osc (phase σ) t‖ := by
            rw [hsplit2]
            exact norm_add_le _ _
          have hfin : ‖∫ t in a..(Real.log (σ/(4*Real.pi))), osc (phase σ) t‖
                + ‖∫ t in (Real.log (σ/(4*Real.pi)))..b, osc (phase σ) t‖
              ≤ 10000 * (1 + |σ|) ^ (-(1/2:ℝ)) := by
            rw [abs_of_pos hσpos]
            linarith [hpiece1, hpiece2, conv_B hσ1]
          exact hstep.trans hfin
    · -- Case C: `σ < -2π e^a`
      have hσneg : σ < 0 := by linarith
      have hbnd : ∀ x ∈ Set.Icc a b, |σ| ≤ |deriv (phase σ) x| := by
        intro x hx
        have hnn : (0:ℝ) ≤ 2 * Real.pi * Real.exp x := by positivity
        have hle : σ - 2 * Real.pi * Real.exp x < 0 := by linarith
        have h2 : deriv (phase σ) x = σ - 2 * Real.pi * Real.exp x := by rw [deriv_phase]
        have h3 : |σ - 2 * Real.pi * Real.exp x| = -(σ - 2 * Real.pi * Real.exp x) :=
          abs_of_neg hle
        have h4 : |σ| = -σ := abs_of_neg hσneg
        rw [h2, h3, h4]
        linarith
      have h4 : ‖∫ t in a..b, osc (phase σ) t‖ ≤ 4 / |σ| :=
        vdc_first_deriv_phase hab (abs_pos.mpr (ne_of_lt hσneg)) hbnd
      refine h4.trans ?_
      have h1 : (1:ℝ) ≤ |σ| := by rw [abs_of_neg hσneg]; linarith
      exact conv_N h1

/-! ## The main theorem -/

theorem oscF_interval_bound : ∃ C : ℝ, 0 < C ∧ ∀ (V W σ : ℝ), 1 ≤ V → V ≤ W →
    ‖∫ v in V..W, Work.GM.S2.oscF σ v‖ ≤ C * (1 + |σ|) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨10000, by norm_num, ?_⟩
  intro V W σ hV hVW
  have hVpos : 0 < V := lt_of_lt_of_le one_pos hV
  have hWpos : 0 < W := lt_of_lt_of_le hVpos hVW
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (E := ℂ)
      (f := Real.exp) (f' := Real.exp) (g := oscF σ)
      (a := Real.log V) (b := Real.log W)
      Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x)
      (fun x _ => Real.exp_nonneg x)
  rw [Real.exp_log hVpos, Real.exp_log hWpos] at hsub
  have hcongr : ∫ s in Real.log V..Real.log W, Real.exp s • (oscF σ ∘ Real.exp) s
      = ∫ s in Real.log V..Real.log W, osc (phase σ) s := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Function.comp_apply]
    exact oscF_smul_exp σ s
  have hmain : ‖∫ v in V..W, oscF σ v‖ = ‖∫ s in Real.log V..Real.log W, osc (phase σ) s‖ := by
    rw [← hsub, hcongr]
  rw [hmain]
  exact phase_integral_bound_aux (Real.log V) (Real.log W) σ (Real.log_nonneg hV)
    (Real.log_le_log hVpos hVW)

end

end Work.GM.S2
