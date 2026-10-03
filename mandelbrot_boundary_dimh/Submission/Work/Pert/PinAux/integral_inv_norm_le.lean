import Mathlib

/-!
# `Work.Pert.PinAux.integral_inv_norm_le`

A quantitative bound for the integral of the reciprocal of the modulus of a point on a
vertical line in `ℂ`:

`∫_a^b dx / ‖x + i y‖ ≤ 2 + 2 log (max (max |a| |b|) r / r)`

whenever `a ≤ b`, `r > 0` and `r ≤ ‖x + i y‖` for all `x ∈ [a, b]`.

The proof runs through the auxiliary functions `x ↦ 1 / max |x| r` (an upper bound for the
integrand on `[a, b]`):

* the integrand is at most `1 / max |x| r` on `[a, b]`, because
  `|x| ≤ ‖x + i y‖` and `r ≤ ‖x + i y‖`;
* the interval is enlarged to the symmetric interval `[-B, B]`, `B = max |a| |b|`;
* the resulting integral is even, hence twice the integral over `[0, B]`;
* on `[0, B]` the elementary estimate `∫_0^B dx / max x r ≤ 1 + log (max B r / r)` holds
  (with equality for `B ≥ r`).
-/

open MeasureTheory

namespace Work.Pert.PinAux

/-- The modulus of `x + y * I` (for real `x`, `y`) equals `sqrt (x ^ 2 + y ^ 2)`. -/
private lemma norm_ofReal_add_mul_I (x y : ℝ) :
    ‖(x : ℂ) + y * Complex.I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  have hsq : ‖(x : ℂ) + y * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Pointwise comparison: if `r ≤ ‖x + i y‖` and `r > 0` then
`1 / ‖x + i y‖ ≤ 1 / max |x| r`. -/
private lemma inv_norm_le_inv_max_abs (y : ℝ) {r x : ℝ} (hr : 0 < r)
    (h : r ≤ ‖(x : ℂ) + y * Complex.I‖) :
    1 / ‖(x : ℂ) + y * Complex.I‖ ≤ 1 / max |x| r := by
  have hxle : |x| ≤ ‖(x : ℂ) + y * Complex.I‖ := by
    rw [norm_ofReal_add_mul_I, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  exact one_div_le_one_div_of_le (lt_of_lt_of_le hr (le_max_right |x| r)) (max_le hxle h)

/-- The integrand `x ↦ 1 / max |x| r` is continuous (its denominator is at least `r > 0`). -/
private lemma continuous_one_div_max_abs (r : ℝ) (hr : 0 < r) :
    Continuous fun x : ℝ => 1 / max |x| r := by
  have hpos : ∀ x : ℝ, max |x| r ≠ 0 := fun x =>
    ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  have hh : Continuous fun x : ℝ => (max |x| r)⁻¹ :=
    ((continuous_id.abs).max continuous_const).inv₀ hpos
  simpa [one_div] using hh

/-- The one-sided integral bound `∫_0^B dx / max x r ≤ 1 + log (max B r / r)`. -/
private lemma integral_inv_max_abs_zero {B r : ℝ} (hr : 0 < r) (hB : 0 ≤ B) :
    (∫ x in (0:ℝ)..B, 1 / max x r) ≤ 1 + Real.log (max B r / r) := by
  rcases le_or_gt B r with hBr | hrB
  · have hcongr : (∫ x in (0:ℝ)..B, 1 / max x r) = ∫ x in (0:ℝ)..B, 1 / r := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hB] at hx
      show 1 / max x r = 1 / r
      rw [max_eq_right (le_trans hx.2 hBr)]
    have hval : (∫ x in (0:ℝ)..B, 1 / r) = B / r := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul, div_eq_mul_inv]
    have hle : B / r ≤ 1 := (div_le_one hr).mpr hBr
    have hrhs : 1 + Real.log (max B r / r) = 1 := by
      rw [max_eq_right hBr, div_self (ne_of_gt hr), Real.log_one]
      norm_num
    rw [hcongr, hval, hrhs]
    exact hle
  · have hcont : Continuous fun x : ℝ => 1 / max x r := by
      have hpos : ∀ x : ℝ, max x r ≠ 0 := fun x =>
        ne_of_gt (lt_of_lt_of_le hr (le_max_right x r))
      have hh : Continuous fun x : ℝ => (max x r)⁻¹ :=
        (continuous_id.max continuous_const).inv₀ hpos
      simpa [one_div] using hh
    have h1 : IntervalIntegrable (fun x : ℝ => 1 / max x r) volume (0:ℝ) r :=
      hcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => 1 / max x r) volume r B :=
      hcont.intervalIntegrable _ _
    have hadj := intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hleft : (∫ x in (0:ℝ)..r, 1 / max x r) = 1 := by
      have hcongr : (∫ x in (0:ℝ)..r, 1 / max x r) = ∫ x in (0:ℝ)..r, 1 / r := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (le_of_lt hr)] at hx
        show 1 / max x r = 1 / r
        rw [max_eq_right hx.2]
      rw [hcongr, intervalIntegral.integral_const]
      simp [smul_eq_mul, div_eq_mul_inv]
      field_simp
    have hright : (∫ x in r..B, 1 / max x r) = Real.log (B / r) := by
      have hcongr : (∫ x in r..B, 1 / max x r) = ∫ x in r..B, 1 / x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (le_of_lt hrB)] at hx
        show 1 / max x r = 1 / x
        rw [max_eq_left hx.1]
      rw [hcongr, integral_one_div_of_pos hr (lt_trans hr hrB)]
    have hval : (∫ x in (0:ℝ)..B, 1 / max x r) = 1 + Real.log (B / r) := by
      rw [← hadj, hleft, hright]
    rw [hval, max_eq_left (le_of_lt hrB)]

theorem integral_inv_norm_le {a b y r : ℝ} (hr : 0 < r) (hab : a ≤ b)
    (hnorm : ∀ x ∈ Set.Icc a b, r ≤ ‖(x : ℂ) + y * Complex.I‖) :
    (∫ x in a..b, 1 / ‖(x : ℂ) + y * Complex.I‖)
      ≤ 2 + 2 * Real.log (max (max |a| |b|) r / r) := by
  set B : ℝ := max |a| |b| with hBdef
  have hB0 : 0 ≤ B := le_trans (abs_nonneg a) (le_max_left _ _)
  have hbB : b ≤ B := le_trans (le_abs_self b) (le_max_right _ _)
  have hnbB : -B ≤ a := by
    have h1 : -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
    have h2 : -|a| ≤ a := neg_abs_le a
    linarith [hBdef, h1, h2]
  have hfcont : Continuous fun x : ℝ => 1 / max |x| r := continuous_one_div_max_abs r hr
  have hfint : IntervalIntegrable (fun x : ℝ => 1 / max |x| r) volume a b :=
    hfcont.intervalIntegrable a b
  have hfintB : IntervalIntegrable (fun x : ℝ => 1 / max |x| r) volume (-B) B :=
    hfcont.intervalIntegrable (-B) B
  have hfint0 : IntervalIntegrable (fun x : ℝ => 1 / max |x| r) volume (-B) 0 :=
    hfcont.intervalIntegrable (-B) 0
  have hfint1 : IntervalIntegrable (fun x : ℝ => 1 / max |x| r) volume 0 B :=
    hfcont.intervalIntegrable 0 B
  have hgs : ContinuousOn (fun x : ℝ => 1 / ‖(x : ℂ) + y * Complex.I‖) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun x : ℝ => ‖(x : ℂ) + y * Complex.I‖) (Set.Icc a b) :=
      ((Complex.continuous_ofReal.add continuous_const).norm).continuousOn
    have hne : ∀ x ∈ Set.Icc a b, ‖(x : ℂ) + y * Complex.I‖ ≠ 0 :=
      fun x hx => ne_of_gt (lt_of_lt_of_le hr (hnorm x hx))
    have h2 : ContinuousOn (fun x : ℝ => (‖(x : ℂ) + y * Complex.I‖)⁻¹) (Set.Icc a b) :=
      h1.inv₀ hne
    simpa [one_div] using h2
  have hgint : IntervalIntegrable (fun x : ℝ => 1 / ‖(x : ℂ) + y * Complex.I‖) volume a b :=
    hgs.intervalIntegrable_of_Icc hab
  -- Step 1: compare the integrand pointwise with `1 / max |x| r`.
  have step1 : (∫ x in a..b, 1 / ‖(x : ℂ) + y * Complex.I‖)
      ≤ ∫ x in a..b, 1 / max |x| r :=
    intervalIntegral.integral_mono_on hab hgint hfint
      (fun x hx => inv_norm_le_inv_max_abs y hr (hnorm x hx))
  -- Step 2: enlarge the interval of integration to `[-B, B]`.
  have step2 : (∫ x in a..b, 1 / max |x| r) ≤ ∫ x in (-B)..B, 1 / max |x| r :=
    intervalIntegral.integral_mono_interval hnbB hab hbB
      (by filter_upwards with x
          exact div_nonneg zero_le_one (le_trans (le_of_lt hr) (le_max_right |x| r)))
      hfintB
  -- Step 3: evenness gives twice the integral over `[0, B]`.
  have hsym : (∫ x in (-B)..B, 1 / max |x| r) = 2 * ∫ x in (0:ℝ)..B, 1 / max |x| r := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals hfint0 hfint1
    have hneg : (∫ x in (-B)..0, 1 / max |x| r) = ∫ x in (0:ℝ)..B, 1 / max |x| r := by
      have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := B)
        (f := fun x : ℝ => 1 / max |x| r)
      simp only [neg_zero] at h
      rw [show (∫ x in (0:ℝ)..B, (fun x : ℝ => 1 / max |x| r) (-x))
            = ∫ x in (0:ℝ)..B, 1 / max |x| r from
        intervalIntegral.integral_congr (fun x _ => by simp [abs_neg])] at h
      exact h.symm
    rw [← hadj, hneg]
    ring
  -- Step 4: on `[0, B]` we have `|x| = x`.
  have h4 : (∫ x in (0:ℝ)..B, 1 / max |x| r) = ∫ x in (0:ℝ)..B, 1 / max x r := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hB0] at hx
    show 1 / max |x| r = 1 / max x r
    rw [abs_of_nonneg hx.1]
  -- Step 5: the elementary one-sided estimate.
  have h5 := integral_inv_max_abs_zero (B := B) hr hB0
  calc (∫ x in a..b, 1 / ‖(x : ℂ) + y * Complex.I‖)
      ≤ ∫ x in a..b, 1 / max |x| r := step1
    _ ≤ ∫ x in (-B)..B, 1 / max |x| r := step2
    _ = 2 * ∫ x in (0:ℝ)..B, 1 / max |x| r := hsym
    _ = 2 * ∫ x in (0:ℝ)..B, 1 / max x r := by rw [h4]
    _ ≤ 2 * (1 + Real.log (max B r / r)) := by
        exact mul_le_mul_of_nonneg_left h5 (by norm_num)
    _ = 2 + 2 * Real.log (max B r / r) := by ring

end Work.Pert.PinAux
