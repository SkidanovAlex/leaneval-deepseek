/-
# `APSwitchUpper.riPhiEnvBasic` — elementary properties of the envelope `riPhiEnv`

The window sum of `window_env_sum` is controlled by the explicit envelope `riPhiEnv`
(`APSwitchUpper/riPhiEnvDefs.lean`).  This module collects the elementary structural facts
used by the numerical window bound:

* `Aprime` is differentiable with the stated derivative and increasing on `[2,4]`;
* `envNum` is antitone, and `riPhiEnv` is antitone, nonnegative and at most `1` on `[11/5,∞)`;
* `riPhiEnv` is continuous on `(0,∞)`;
* the rational lower/upper bounds `logLowRat`/`logUpRat` for `log` coming from the odd Taylor
  series of `artanh`, together with the elementary integral rules for convex functions
  (midpoint and trapezoid).
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvDefs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.convexOn_aprimeIntegrand

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory Real

/-! ## §1  `Aprime` -/

private lemma continuousAt_aprimeIntegrand {u : ℝ} (hu : 1 < u) :
    ContinuousAt (fun v : ℝ => Real.log (3 / (v - 1)) / v) u := by
  have h1 : ContinuousAt (fun v : ℝ => 3 / (v - 1)) u :=
    ContinuousAt.div continuousAt_const (by fun_prop) (by linarith)
  exact ContinuousAt.div (h1.log (by positivity)) continuousAt_id (by linarith)

private lemma continuousOn_aprimeIntegrand {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun v : ℝ => Real.log (3 / (v - 1)) / v) (Set.uIcc a b) := by
  intro v hv
  rw [Set.uIcc_of_le hab] at hv
  exact (continuousAt_aprimeIntegrand (by linarith [hv.1, h2])).continuousWithinAt

theorem hasDerivAt_Aprime {x : ℝ} (hx : 2 < x) :
    HasDerivAt Aprime (Real.log (3 / (x - 1)) / x) x := by
  unfold Aprime
  refine intervalIntegral.integral_hasDerivAt_right
    ((continuousOn_aprimeIntegrand (by norm_num) hx.le).intervalIntegrable) ?_
    (continuousAt_aprimeIntegrand (by linarith))
  exact ContinuousAt.stronglyMeasurableAtFilter
    (f := fun v : ℝ => Real.log (3 / (v - 1)) / v) (s := Set.Ioi 1) (μ := volume)
    isOpen_Ioi (fun v hv => continuousAt_aprimeIntegrand hv) x (Set.mem_Ioi.mpr (by linarith))

theorem Aprime_sub_eq {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    Aprime b - Aprime a = ∫ v in a..b, Real.log (3 / (v - 1)) / v := by
  have h1 : IntervalIntegrable (fun v : ℝ => Real.log (3 / (v - 1)) / v) volume (2 : ℝ) a :=
    (continuousOn_aprimeIntegrand (by norm_num) h2).intervalIntegrable
  have h2' : IntervalIntegrable (fun v : ℝ => Real.log (3 / (v - 1)) / v) volume a b :=
    (continuousOn_aprimeIntegrand h2 hab).intervalIntegrable
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2'
  unfold Aprime
  linarith [h]

theorem Aprime_monoOn : MonotoneOn Aprime (Set.Icc 2 4) := by
  intro a ha b hb hab
  have h := Aprime_sub_eq ha.1 hab
  have hnn : 0 ≤ ∫ v in a..b, Real.log (3 / (v - 1)) / v := by
    refine intervalIntegral.integral_nonneg hab (fun v hv => ?_)
    have hv1 : 1 < v := by linarith [hv.1, ha.1]
    have h3 : 1 ≤ 3 / (v - 1) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < v - 1)]
      linarith [hv.2, hb.2]
    have := Real.log_nonneg h3
    positivity
  linarith [h, hnn]

/-! ## §2  `envNum` -/

private lemma continuousOn_Aprime_Icc : ContinuousOn Aprime (Set.Icc 2 4) := by
  intro b₀ hb₀
  exact intervalIntegral.continuousWithinAt_primitive (μ := volume) (a := (2 : ℝ))
    (b₁ := (2 : ℝ)) (b₂ := (4 : ℝ)) (b₀ := b₀) (by simp)
    ((continuousOn_aprimeIntegrand (by norm_num) (by norm_num)).intervalIntegrable)

private lemma continuousOn_aprimeShift : ContinuousOn (fun t : ℝ => Aprime (t - 1)) (Set.Icc 3 5) :=
  continuousOn_Aprime_Icc.comp ((continuousOn_id.sub continuousOn_const))
    (fun t ht => by
      rw [Set.mem_Icc] at ht ⊢
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- The closed form of the derivative of `envNum` on `(3,5)`. -/
noncomputable def envNumDeriv (s : ℝ) : ℝ :=
  -(3 + envC) * (Real.log (3 / (s - 2)) / (s - 1)) + (4 - envT) / (s - 1) - 1

theorem envNum_eventuallyEq {s : ℝ} (h3 : 3 < s) (h5 : s < 5) :
    envNum =ᶠ[nhds s] (fun t : ℝ => envC - ((3 + envC) * Aprime (t - 1)
      + (envT - 4) * Real.log ((t - 1) / 2) + ((t - 1) - 2))) := by
  filter_upwards [Ioo_mem_nhds h3 h5] with t ht
  have h1 : min (t - 1) 4 = t - 1 := min_eq_left (by linarith [ht.2] : t - 1 ≤ 4)
  simp only [envNum, h1]

theorem hasDerivAt_envNum {s : ℝ} (h3 : 3 < s) (h5 : s < 5) :
    HasDerivAt envNum (envNumDeriv s) s := by
  have h2 : HasDerivAt (fun t : ℝ => t - 1) (1 : ℝ) s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have h1 : HasDerivAt (fun t : ℝ => Aprime (t - 1))
      (Real.log (3 / (s - 2)) / (s - 1)) s := by
    have h := (hasDerivAt_Aprime (x := s - 1) (by linarith)).comp s h2
    change HasDerivAt (fun t : ℝ => Aprime (t - 1)) _ s at h
    refine h.congr_deriv ?_
    rw [show s - 1 - 1 = s - 2 by ring, mul_one]
  have hlog : HasDerivAt (fun t : ℝ => Real.log ((t - 1) / 2)) (1 / (s - 1)) s := by
    have hdiv : HasDerivAt (fun t : ℝ => (t - 1) / 2) (1 / 2) s := by
      simpa using (h2.div_const 2)
    have hne : (s - 1) / 2 ≠ 0 := by linarith
    refine (hdiv.log hne).congr_deriv ?_
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  have hlin : HasDerivAt (fun t : ℝ => (t - 1) - 2) (1 : ℝ) s := by
    simpa using (h2.sub_const 2)
  have hF : HasDerivAt (fun t : ℝ => envC - ((3 + envC) * Aprime (t - 1)
      + (envT - 4) * Real.log ((t - 1) / 2) + ((t - 1) - 2)))
      (envNumDeriv s) s := by
    have hsum := ((h1.const_mul (3 + envC)).add (hlog.const_mul (envT - 4))).add hlin
    refine (hasDerivAt_const (x := s) envC).sub (hsum.congr_of_eventuallyEq ?_) |>.congr_deriv ?_
    · filter_upwards with t
      simp only [Pi.add_apply]
    · rw [envNumDeriv]
      field_simp
      ring
  exact hF.congr_of_eventuallyEq (envNum_eventuallyEq h3 h5)

theorem deriv_envNum {s : ℝ} (h3 : 3 < s) (h5 : s < 5) : deriv envNum s = envNumDeriv s :=
  (hasDerivAt_envNum h3 h5).deriv

theorem envNumDeriv_nonpos {s : ℝ} (h3 : 3 < s) (h5 : s < 5) : envNumDeriv s ≤ 0 := by
  have hx1 : 0 < s - 1 := by linarith
  have hlog : 1 - (s - 2) / 3 ≤ Real.log (3 / (s - 2)) := by
    have h3' : (0 : ℝ) < 3 / (s - 2) := div_pos (by norm_num) (by linarith)
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h3')
    rw [Real.log_inv] at h
    have h' : (3 / (s - 2))⁻¹ = (s - 2) / 3 := by rw [inv_div]
    rw [h'] at h
    linarith
  have hkey : (4 - envT) - (s - 1) ≤ (3 + envC) * Real.log (3 / (s - 2)) := by
    have h1 : (3 + envC) * (1 - (s - 2) / 3) ≤ (3 + envC) * Real.log (3 / (s - 2)) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num [envC])
    have hnum : (4 - envT) - (s - 1) ≤ (3 + envC) * (1 - (s - 2) / 3) := by
      simp only [envC, envT]
      linarith
    linarith [h1, hnum]
  have heq : -(3 + envC) * (Real.log (3 / (s - 2)) / (s - 1)) + (4 - envT) / (s - 1)
      = ((4 - envT) - (3 + envC) * Real.log (3 / (s - 2))) / (s - 1) := by
    field_simp
    ring
  rw [envNumDeriv, heq, sub_nonpos, div_le_iff₀ hx1]
  linarith [hkey]

theorem continuousOn_envNum_Icc : ContinuousOn envNum (Set.Icc 3 5) := by
  have heq : Set.EqOn envNum (fun t : ℝ => envC - ((3 + envC) * Aprime (t - 1)
      + (envT - 4) * Real.log ((t - 1) / 2) + ((t - 1) - 2))) (Set.Icc 3 5) := by
    intro t ht
    have h1 : min (t - 1) 4 = t - 1 := min_eq_left (by linarith [ht.2] : t - 1 ≤ 4)
    simp only [envNum, h1]
  have hdiv2 : ContinuousOn (fun t : ℝ => (t - 1) / 2) (Set.Icc 3 5) :=
    (continuousOn_id.sub continuousOn_const).div_const 2
  have hcontL : ContinuousOn (fun t : ℝ => Real.log ((t - 1) / 2)) (Set.Icc 3 5) := by
    refine ContinuousOn.log hdiv2 ?_
    intro t ht
    exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < (t - 1) / 2)
  have hlin2 : ContinuousOn (fun t : ℝ => (t - 1) - 2) (Set.Icc 3 5) :=
    (continuousOn_id.sub continuousOn_const).sub continuousOn_const
  have hmain : ContinuousOn (fun t : ℝ => envC - ((3 + envC) * Aprime (t - 1)
      + (envT - 4) * Real.log ((t - 1) / 2) + ((t - 1) - 2))) (Set.Icc 3 5) :=
    continuousOn_const.sub
      (((continuousOn_aprimeShift.const_mul (3 + envC)).add
        (hcontL.const_mul (envT - 4))).add hlin2)
  exact hmain.congr heq

theorem envNum_antiOn_Icc : AntitoneOn envNum (Set.Icc 3 5) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 3 5) continuousOn_envNum_Icc ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_envNum hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [deriv_envNum hx.1 hx.2]
    exact envNumDeriv_nonpos hx.1 hx.2

theorem envNum_three : envNum 3 = envC := by
  have h1 : min ((3 : ℝ) - 1) 4 = (2 : ℝ) := by norm_num
  simp only [envNum, h1, Aprime_two]
  norm_num

theorem envNum_of_five_le {s : ℝ} (hs : 5 ≤ s) :
    envNum s = envC - ((3 + envC) * Aprime 4 + (envT - 4) * Real.log 2 + 2) := by
  have h1 : min (s - 1) 4 = (4 : ℝ) := min_eq_right (by linarith : (4 : ℝ) ≤ s - 1)
  simp only [envNum, h1]
  norm_num

theorem envNum_antiOn : AntitoneOn envNum (Set.Ici 3) := by
  intro a ha b hb hab
  by_cases hb5 : b ≤ 5
  · exact envNum_antiOn_Icc ⟨ha, by linarith⟩ ⟨hb, hb5⟩ hab
  · push_neg at hb5
    have hb5' : envNum b = envNum 5 := by
      rw [envNum_of_five_le (le_of_lt hb5), envNum_of_five_le (by norm_num : (5 : ℝ) ≤ 5)]
    by_cases ha5 : a ≤ 5
    · have h1 : envNum 5 ≤ envNum a := envNum_antiOn_Icc ⟨ha, ha5⟩ ⟨by norm_num, by norm_num⟩ ha5
      rw [hb5']; exact h1
    · rw [not_le] at ha5
      have ha5' : envNum a = envNum 5 := by
        rw [envNum_of_five_le (le_of_lt ha5), envNum_of_five_le (by norm_num : (5 : ℝ) ≤ 5)]
      rw [hb5', ha5']


/-! ## §3  Rational bounds for logarithms -/

/-- `0.6931471 ≤ log 2`. -/
theorem log_two_lower : (0.6931471 : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1/3 : ℝ)) (by norm_num) (by norm_num) 10
  rw [show (1 + (1:ℝ)/3) / (1 - 1/3) = 2 by norm_num] at h
  have h2 : (0.6931471 : ℝ) ≤ 2 * ∑ i ∈ Finset.range 10, (1/3 : ℝ) ^ (2*i+1) / (2*i+1) := by
    norm_num
  linarith

/-- `log 3 ≤ 1.0986124`. -/
theorem log_three_upper : Real.log 3 ≤ (1.0986124 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1/2 : ℝ)) (by norm_num) (by norm_num) 13
  rw [show (1 + (1:ℝ)/2) / (1 - 1/2) = 3 by norm_num] at h
  have h2 : 2 * (∑ i ∈ Finset.range 13, (1/2 : ℝ) ^ (2*i+1) / (2*i+1)
      + (1/2 : ℝ) ^ (2*13+1) / (1 - (1/2)^2)) ≤ 1.0986124 := by norm_num
  linarith

/-- The five-term odd Taylor lower bound for `log`. -/
noncomputable def logLowRat (z : ℝ) : ℝ :=
  let w := (z - 1) / (z + 1)
  2 * (w + w^3/3 + w^5/5 + w^7/7 + w^9/9)

/-- The five-term odd Taylor upper bound for `log` (with the geometric tail). -/
noncomputable def logUpRat (z : ℝ) : ℝ :=
  let w := (z - 1) / (z + 1)
  2 * (w + w^3/3 + w^5/5 + w^7/7 + w^9/9 + w^11/(1 - w^2))

theorem logLowRat_le {z : ℝ} (h1 : 1 ≤ z) : logLowRat z ≤ Real.log z := by
  rcases eq_or_lt_of_le h1 with hz1 | hz
  · rw [← hz1]; simp [logLowRat]
  have hx0 : 0 ≤ (z - 1)/(z + 1) := by positivity
  have hx1 : (z - 1)/(z + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := Real.sum_range_le_log_div hx0 hx1 5
  have hx : (1 + (z - 1)/(z + 1))/(1 - (z - 1)/(z + 1)) = z := by field_simp; ring
  rw [hx] at h
  have hsum : ∑ i ∈ Finset.range 5, ((z - 1)/(z + 1)) ^ (2*i+1) / (2*i+1)
      = (z - 1)/(z + 1) + ((z - 1)/(z + 1))^3/3 + ((z - 1)/(z + 1))^5/5
        + ((z - 1)/(z + 1))^7/7 + ((z - 1)/(z + 1))^9/9 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  rw [hsum] at h
  simp only [logLowRat]
  linarith

theorem le_logUpRat {z : ℝ} (h1 : 1 ≤ z) : Real.log z ≤ logUpRat z := by
  rcases eq_or_lt_of_le h1 with hz1 | hz
  · rw [← hz1]; simp [logUpRat]
  have hx0 : 0 ≤ (z - 1)/(z + 1) := by positivity
  have hx1 : (z - 1)/(z + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := Real.log_div_le_sum_range_add hx0 hx1 5
  have hx : (1 + (z - 1)/(z + 1))/(1 - (z - 1)/(z + 1)) = z := by field_simp; ring
  rw [hx] at h
  have hsum : ∑ i ∈ Finset.range 5, ((z - 1)/(z + 1)) ^ (2*i+1) / (2*i+1)
      = (z - 1)/(z + 1) + ((z - 1)/(z + 1))^3/3 + ((z - 1)/(z + 1))^5/5
        + ((z - 1)/(z + 1))^7/7 + ((z - 1)/(z + 1))^9/9 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  rw [hsum] at h
  have hw2 : 0 < 1 - ((z - 1)/(z + 1))^2 := by nlinarith [hx0, hx1]
  simp only [logUpRat]
  linarith

/-! ## §4  The chord, trapezoid and midpoint rules for convex functions -/

/-- The chord of a convex function dominates it. -/
theorem le_chord_of_convexOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f x ≤ f a + (f b - f a) * (x - a) / (b - a) := by
  rcases eq_or_lt_of_le hab with hab0 | hab'
  · subst hab0
    rw [le_antisymm hx.2 hx.1]
    simp
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · subst hxa
    rw [sub_self, mul_zero, zero_div, add_zero]
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · rw [hxb, mul_div_cancel_right₀ _ (by linarith : b - a ≠ 0)]
    linarith
  · have h := hf.secant_mono_aux1 (x := a) (y := x) (z := b)
      (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)
      hxa hxb
    rw [show f a + (f b - f a) * (x - a) / (b - a)
        = ((b - x) * f a + (x - a) * f b) / (b - a) by field_simp; ring]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < b - a)]
    linarith [h]

/-- The trapezoid rule is an upper bound for a convex function. -/
theorem integral_le_trapezoid {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hcont : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x ≤ (b - a) * (f a + f b) / 2 := by
  rcases eq_or_lt_of_le hab with hab0 | hab'
  · subst hab0; simp
  have hchord : ∀ x ∈ Set.Icc a b, f x ≤ f a + (f b - f a) * (x - a) / (b - a) :=
    fun x hx => le_chord_of_convexOn hab hf hx
  have hLI : IntervalIntegrable (fun x : ℝ => f a + (f b - f a) * (x - a) / (b - a))
      volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hI : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable (hcont.mono (by rw [Set.uIcc_of_le hab]))
  have hmono := intervalIntegral.integral_mono_on hab hI hLI hchord
  have hval : ∫ x in a..b, (f a + (f b - f a) * (x - a) / (b - a))
      = (b - a) * (f a + f b) / 2 := by
    rw [show (∫ x in a..b, (f a + (f b - f a) * (x - a) / (b - a)))
        = ∫ x in a..b, ((f a - (f b - f a) * a / (b - a))
            + ((f b - f a) / (b - a)) * x) by
      refine intervalIntegral.integral_congr (fun x _ => by ring)]
    rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) a b)
        (Continuous.intervalIntegrable (by fun_prop) a b),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    field_simp
    ring
  linarith [hmono, hval]

/-- The midpoint rule is a lower bound for a function with the midpoint Jensen property. -/
theorem midpoint_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hj : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f ((x+y)/2) ≤ (f x + f y)/2)
    (hint : IntervalIntegrable f volume a b) :
    (b - a) * f ((a+b)/2) ≤ ∫ x in a..b, f x := by
  have hA : ∫ t in (-(b-a)/2)..((b-a)/2), f ((a+b)/2 + t) = ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_comp_add_left f ((a+b)/2)]
    congr 1 <;> ring_nf
  have hB : ∫ t in (-(b-a)/2)..((b-a)/2), f ((a+b)/2 - t) = ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_comp_sub_left f ((a+b)/2)]
    congr 1 <;> ring_nf
  have hI1 : IntervalIntegrable (fun t : ℝ => f ((a+b)/2 + t)) volume (-(b-a)/2) ((b-a)/2) := by
    have h := hint.comp_add_left ((a+b)/2) (by simp)
    have h2 : a - (a+b)/2 = -(b-a)/2 := by ring
    have h3 : b - (a+b)/2 = (b-a)/2 := by ring
    rw [h2, h3] at h
    exact h
  have hI2 : IntervalIntegrable (fun t : ℝ => f ((a+b)/2 - t)) volume (-(b-a)/2) ((b-a)/2) := by
    have h := hint.comp_sub_left ((a+b)/2) (by simp)
    have h2 : (a+b)/2 - a = (b-a)/2 := by ring
    have h3 : (a+b)/2 - b = -(b-a)/2 := by ring
    rw [h2, h3] at h
    exact h.symm
  have hle : (-(b-a)/2) ≤ (b-a)/2 := by linarith
  have hpoint : ∀ t ∈ Set.Icc (-(b-a)/2) ((b-a)/2),
      2 * f ((a+b)/2) ≤ f ((a+b)/2 + t) + f ((a+b)/2 - t) := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have h1 : (a+b)/2 + t ∈ Set.Icc a b := by
      rw [Set.mem_Icc]; constructor <;> linarith [ht.1, ht.2]
    have h2 : (a+b)/2 - t ∈ Set.Icc a b := by
      rw [Set.mem_Icc]; constructor <;> linarith [ht.1, ht.2]
    have h3 := hj ((a+b)/2 + t) h1 ((a+b)/2 - t) h2
    have h4 : (((a+b)/2 + t) + ((a+b)/2 - t))/2 = (a+b)/2 := by ring
    rw [h4] at h3
    linarith
  have hmain := intervalIntegral.integral_mono_on hle
    (Continuous.intervalIntegrable (by fun_prop) _ _) (hI1.add hI2) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hI1 hI2, hA, hB] at hmain
  simp only [smul_eq_mul] at hmain
  linarith [hmain]


/-! ## §5  The numerical upper bound for `Aprime 4` and positivity of `envNum` -/

private lemma envC_pos : (0:ℝ) < envC := by norm_num [envC]

private lemma continuousOn_aprimeIntegrand_Icc {a b : ℝ} (ha : 2 ≤ a) (hb : b ≤ 4) :
    ContinuousOn (fun x : ℝ => Real.log (3/(x-1))/x) (Set.Icc a b) := by
  have hpos : ∀ x ∈ Set.Icc a b, 0 < (x:ℝ) - 1 := by
    intro x hx; rw [Set.mem_Icc] at hx; linarith [hx.1, ha]
  refine ContinuousOn.div ?_ continuousOn_id
    (fun x hx => ne_of_gt (by linarith [hpos x hx]))
  refine ContinuousOn.log ?_ (fun x hx => ne_of_gt (div_pos (by norm_num) (hpos x hx)))
  exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    (fun x hx => ne_of_gt (hpos x hx))

private lemma envUp_gt (k : ℕ) : (0:ℝ) < 2 + (k:ℝ)/8 := by positivity

/-- `Aprime 4 ≤ 0.3576` via the trapezoid rule for the convex integrand on `[2,4]`. -/
theorem Aprime_four_le : Aprime 4 ≤ (0.3576 : ℝ) := by
  have hA4 : Aprime 4 = ∫ x in (2:ℝ)..4, Real.log (3/(x-1))/x := by
    have h := Aprime_sub_eq (a := 2) (b := 4) (by norm_num) (by norm_num)
    rw [Aprime_two, sub_zero] at h
    exact h
  rw [hA4]
  have hdvd : ∀ k : ℕ, k < 16 → (2:ℝ) + (k:ℝ)/8 ≤ 2 + ((k:ℝ)+1)/8 := by
    intro k hk
    have hk' : (k:ℝ) < 16 := by exact_mod_cast hk
    linarith
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => Real.log (3/(x-1))/x) (a := fun k : ℕ => 2 + (k:ℝ)/8) (n := 16)
    (fun k hk => ContinuousOn.intervalIntegrable (μ := volume) (by
      simp only [Nat.cast_add, Nat.cast_one]
      rw [Set.uIcc_of_le (hdvd k hk)]
      exact continuousOn_aprimeIntegrand_Icc (by
          have hknn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith)
        (by
          have hk' : (k:ℝ) ≤ 15 := by exact_mod_cast (by omega : k ≤ 15)
          linarith)))
  have h0 : (2:ℝ) + ((0:ℕ):ℝ)/8 = 2 := by norm_num
  have h16 : (2:ℝ) + ((16:ℕ):ℝ)/8 = 4 := by norm_num
  rw [h0, h16] at hsplit
  rw [← hsplit]
  have hb : (∑ k ∈ Finset.range 16, ∫ x in (2 + (k:ℝ)/8)..(2 + (((k+1:ℕ):ℝ))/8),
        Real.log (3/(x-1))/x)
      ≤ ∑ k ∈ Finset.range 16, (1/8) * (logUpRat (3/((2 + (k:ℝ)/8) - 1))/((2 + (k:ℝ)/8))
          + logUpRat (3/((2 + (((k+1:ℕ):ℝ))/8) - 1))/((2 + (((k+1:ℕ):ℝ))/8))) / 2 := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
    have hk16 : k < 16 := Finset.mem_range.mp hk
    have hk15 : (k:ℝ) ≤ 15 := by exact_mod_cast (by omega : k ≤ 15)
    have hle := hdvd k hk16
    have hconv : ConvexOn ℝ (Set.Icc (2 + (k:ℝ)/8) (2 + ((k:ℝ)+1)/8))
        (fun x : ℝ => Real.log (3/(x-1))/x) :=
      convexOn_aprimeIntegrand.subset (fun x hx => by
        rw [Set.mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2, hk15]) (convex_Icc _ _)
    have hcont := continuousOn_aprimeIntegrand_Icc (a := 2 + (k:ℝ)/8)
      (b := 2 + ((k:ℝ)+1)/8)
      (by have hknn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
      (by linarith [hk15])
    have htrap := integral_le_trapezoid hle hconv hcont
    refine le_trans htrap ?_
    have hp1 := envUp_gt k
    have hp2 : (0:ℝ) < 2 + ((k:ℝ)+1)/8 := by positivity
    have hb1 : Real.log (3/((2 + (k:ℝ)/8) - 1)) ≤ logUpRat (3/((2 + (k:ℝ)/8) - 1)) := by
      refine le_logUpRat ?_
      rw [le_div_iff₀ (by linarith : (0:ℝ) < (2 + (k:ℝ)/8) - 1)]
      linarith
    have hb2 : Real.log (3/((2 + ((k:ℝ)+1)/8) - 1))
        ≤ logUpRat (3/((2 + ((k:ℝ)+1)/8) - 1)) := by
      refine le_logUpRat ?_
      rw [le_div_iff₀ (by linarith : (0:ℝ) < (2 + ((k:ℝ)+1)/8) - 1)]
      linarith
    rw [show (2 + ((k:ℝ)+1)/8) - (2 + (k:ℝ)/8) = (1/8 : ℝ) by ring]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (div_le_div_of_nonneg_right hb1 hp1.le)
      (div_le_div_of_nonneg_right hb2 hp2.le)
  refine le_trans hb ?_
  norm_num [logUpRat]

theorem envNum_five_pos : 0 < envNum 5 := by
  have h5 : envNum 5 = envC - ((3 + envC) * Aprime 4 + (envT - 4) * Real.log 2 + 2) :=
    envNum_of_five_le le_rfl
  rw [h5]
  have hA : Aprime 4 ≤ (0.3576 : ℝ) := Aprime_four_le
  have hL : (0.6931471 : ℝ) ≤ Real.log 2 := log_two_lower
  simp only [envC, envT] at hA hL ⊢
  nlinarith [hA, hL]

theorem envNum_pos {s : ℝ} (hs : 3 ≤ s) : 0 < envNum s := by
  by_cases h5 : s ≤ 5
  · have h1 : envNum 5 ≤ envNum s := envNum_antiOn hs (by norm_num) h5
    linarith [h1, envNum_five_pos]
  · have h1 : envNum s = envNum 5 := by
      rw [envNum_of_five_le (le_of_lt (not_le.mp h5)),
        envNum_of_five_le (by norm_num : (5:ℝ) ≤ 5)]
    rw [h1]; exact envNum_five_pos

/-! ## §6  Monotonicity, positivity and continuity of `riPhiEnv` -/

theorem riPhiEnv_antitoneOn : AntitoneOn riPhiEnv (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [Set.mem_Ioi] at hx hy
  by_cases hy3 : y ≤ 3
  · by_cases hx3 : x ≤ 3
    · rw [riPhiEnv_of_le_three hx3, riPhiEnv_of_le_three hy3]
      rw [div_le_div_iff₀ hy hx]
      nlinarith [envC_pos, hxy]
    · exfalso
      linarith [hxy, hy3, not_le.mp hx3]
  · have hy3' : 3 < y := not_le.mp hy3
    rw [riPhiEnv_of_three_le (le_of_lt hy3')]
    by_cases hx3 : x ≤ 3
    · rw [riPhiEnv_of_le_three hx3]
      have h1 : envNum y ≤ envNum 3 := envNum_antiOn (by norm_num) (le_of_lt hy3') (by linarith)
      rw [envNum_three] at h1
      have h2 : (3 - x + envC)/x = (3 + envC)/x - 1 := by field_simp; ring
      rw [h2]
      have h3 : envC/3 ≤ (3 + envC)/x - 1 := by
        rw [le_sub_iff_add_le, le_div_iff₀ hx]
        have h4 : (envC/3 + 1) * x ≤ (envC/3 + 1) * 3 :=
          mul_le_mul_of_nonneg_left hx3 (by norm_num [envC])
        have h5 : (envC/3 + 1) * 3 = envC + 3 := by ring
        linarith [h4, h5]
      have h4 : envNum y / y ≤ envC/3 := by
        rw [div_le_iff₀ (by linarith)]
        have h5 : envC ≤ (envC/3) * y := by
          have h6 : (envC/3) * 3 ≤ (envC/3) * y :=
            mul_le_mul_of_nonneg_left (by linarith) (by norm_num [envC])
          have h7 : (envC/3) * 3 = envC := by ring
          linarith [h6, h7]
        linarith [h1, h5]
      linarith
    · have hx3' : 3 < x := not_le.mp hx3
      rw [riPhiEnv_of_three_le (le_of_lt hx3')]
      have h1 : envNum y ≤ envNum x := envNum_antiOn (le_of_lt hx3') (le_of_lt hy3') hxy
      have h2 : 0 < envNum x := envNum_pos (by linarith)
      rw [div_le_div_iff₀ hy hx]
      nlinarith [h1, h2, hxy]

theorem riPhiEnv_nonneg {s : ℝ} (hs : 11/5 ≤ s) : 0 ≤ riPhiEnv s := by
  by_cases h3 : s ≤ 3
  · rw [riPhiEnv_of_le_three h3]
    refine div_nonneg ?_ (by linarith)
    have hc : envC = 0.5692 := by norm_num [envC]
    rw [hc]; linarith
  · rw [riPhiEnv_of_three_le (le_of_lt (not_le.mp h3))]
    exact le_of_lt (div_pos (envNum_pos (by linarith)) (by linarith))

theorem riPhiEnv_le_one {s : ℝ} (hs : 11/5 ≤ s) : riPhiEnv s ≤ 1 := by
  have h := riPhiEnv_antitoneOn (show (11/5:ℝ) ∈ Set.Ioi 0 by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 11/5) hs) hs
  have h2 : riPhiEnv (11/5) = ((3 - 11/5) + envC)/(11/5) := riPhiEnv_of_le_three (by norm_num)
  rw [h2] at h
  refine le_trans h ?_
  have henvC : envC = 0.5692 := by norm_num [envC]
  rw [henvC]
  norm_num


/-! ## §7  Continuity of `riPhiEnv` -/

private lemma continuousAt_envNum_of_lt_five {x : ℝ} (h3 : 3 < x) (h5 : x < 5) :
    ContinuousAt envNum x :=
  (hasDerivAt_envNum h3 h5).continuousAt

private lemma continuousAt_envNum_of_gt_five {x : ℝ} (h5 : 5 < x) :
    ContinuousAt envNum x := by
  have hev : envNum =ᶠ[nhds x] (fun _ : ℝ => envNum 5) := by
    filter_upwards [isOpen_Ioi.mem_nhds h5] with t ht
    rw [envNum_of_five_le (le_of_lt ht), envNum_of_five_le (by norm_num : (5:ℝ) ≤ 5)]
  exact continuousAt_const.congr hev.symm

theorem continuousAt_riPhiEnv_of_lt_three {x : ℝ} (h0 : 0 < x) (h3 : x < 3) :
    ContinuousAt riPhiEnv x := by
  have hrat : ContinuousAt (fun s : ℝ => ((3 - s) + envC)/s) x :=
    ContinuousAt.div ((continuousAt_const.sub continuousAt_id).add continuousAt_const)
      continuousAt_id (ne_of_gt h0)
  refine hrat.congr ?_
  filter_upwards [isOpen_Iio.mem_nhds h3] with s hs
  exact (riPhiEnv_of_le_three (le_of_lt hs)).symm

theorem continuousAt_riPhiEnv_of_between {x : ℝ} (h3 : 3 < x) (h5 : x < 5) :
    ContinuousAt riPhiEnv x := by
  have henv : ContinuousAt (fun s : ℝ => envNum s / s) x :=
    (continuousAt_envNum_of_lt_five h3 h5).div continuousAt_id (ne_of_gt (by linarith))
  refine henv.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds h3] with s hs
  exact (riPhiEnv_of_three_le (le_of_lt hs)).symm

theorem continuousAt_riPhiEnv_of_gt_five {x : ℝ} (h5 : 5 < x) : ContinuousAt riPhiEnv x := by
  have henv : ContinuousAt (fun s : ℝ => envNum 5 / s) x :=
    continuousAt_const.div continuousAt_id (ne_of_gt (by linarith))
  refine henv.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds h5] with s hs
  rw [Set.mem_Ioi] at hs
  rw [riPhiEnv_of_three_le (by linarith [hs]), envNum_of_five_le (le_of_lt hs),
    envNum_of_five_le (by norm_num : (5:ℝ) ≤ 5)]

private lemma continuousWithinAt_aprimeShift_Icc : ContinuousWithinAt (fun t : ℝ => Aprime (t - 1))
    (Set.Icc 3 5) 3 :=
  (continuousOn_Aprime_Icc.continuousWithinAt (by norm_num))
    |>.comp ((continuousWithinAt_id.sub continuousWithinAt_const))
      (fun t ht => by
        rw [Set.mem_Icc] at ht ⊢
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)

private lemma continuousWithinAt_envNum_Icc_three : ContinuousWithinAt envNum (Set.Icc 3 5) 3 := by
  have hL : ContinuousWithinAt (fun t : ℝ => Real.log ((t - 1) / 2)) (Set.Icc 3 5) 3 :=
    (ContinuousWithinAt.div (continuousWithinAt_id.sub continuousWithinAt_const)
      continuousWithinAt_const (by norm_num)).log (by norm_num)
  have hexp : ContinuousWithinAt (fun t : ℝ => envC - ((3 + envC) * Aprime (t - 1)
      + (envT - 4) * Real.log ((t - 1) / 2) + ((t - 1) - 2))) (Set.Icc 3 5) 3 :=
    continuousWithinAt_const.sub (((continuousWithinAt_aprimeShift_Icc.const_mul _).add
      (hL.const_mul _)).add
      ((continuousWithinAt_id.sub continuousWithinAt_const).sub continuousWithinAt_const))
  refine ContinuousWithinAt.congr (f := fun t : ℝ => envC - ((3 + envC) * Aprime (t - 1)
      + (envT - 4) * Real.log ((t - 1) / 2) + ((t - 1) - 2))) hexp ?_ ?_
  · intro t ht
    rw [Set.mem_Icc] at ht
    have h1 : min (t - 1) 4 = t - 1 := min_eq_left (by linarith [ht.2])
    simp only [envNum, h1]
  · have h1 : min ((3:ℝ) - 1) 4 = (2:ℝ) := by norm_num
    simp only [envNum, h1]
    norm_num

private lemma continuousWithinAt_envNum_ge_five {x : ℝ} (h5 : 5 ≤ x) :
    ContinuousWithinAt envNum (Set.Ici 5) x := by
  have hev : envNum =ᶠ[nhdsWithin x (Set.Ici 5)] (fun _ : ℝ => envNum 5) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [envNum_of_five_le ht, envNum_of_five_le (by norm_num : (5:ℝ) ≤ 5)]
  refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ : ℝ => envNum 5)
    continuousAt_const.continuousWithinAt hev ?_
  rw [envNum_of_five_le h5, envNum_of_five_le (by norm_num : (5:ℝ) ≤ 5)]

theorem continuousAt_riPhiEnv_three : ContinuousAt riPhiEnv 3 := by
  have hrat : ContinuousAt (fun s : ℝ => ((3 - s) + envC)/s) 3 :=
    ContinuousAt.div ((continuousAt_const.sub continuousAt_id).add continuousAt_const)
      continuousAt_id (by norm_num)
  have h1 : ContinuousWithinAt riPhiEnv (Set.Iic 3) 3 := by
    refine ContinuousWithinAt.congr (f := fun s : ℝ => ((3 - s) + envC)/s)
      hrat.continuousWithinAt (fun y hy => riPhiEnv_of_le_three hy) ?_
    exact riPhiEnv_of_le_three le_rfl
  have h2 : ContinuousWithinAt riPhiEnv (Set.Icc 3 5) 3 := by
    have henv : ContinuousWithinAt (fun s : ℝ => envNum s / s) (Set.Icc 3 5) 3 :=
      continuousWithinAt_envNum_Icc_three.div continuousWithinAt_id (by norm_num)
    refine ContinuousWithinAt.congr (f := fun s : ℝ => envNum s / s) henv
      (fun y hy => riPhiEnv_of_three_le hy.1) ?_
    exact riPhiEnv_of_three_le le_rfl
  have hu := h1.union h2
  refine hu.continuousAt (Filter.mem_of_superset (Iic_mem_nhds (by norm_num : (3:ℝ) < 5)) ?_)
  intro y hy
  by_cases h3 : y ≤ 3
  · exact Or.inl h3
  · exact Or.inr ⟨le_of_lt (lt_of_not_ge h3), hy⟩

theorem continuousAt_riPhiEnv_five : ContinuousAt riPhiEnv 5 := by
  have henv : ContinuousWithinAt (fun s : ℝ => envNum s / s) (Set.Icc 3 5) 5 :=
    (continuousOn_envNum_Icc.div continuousOn_id
      (fun s hs => by have h := hs.1; simp only [id_eq]; linarith)).continuousWithinAt (by norm_num)
  have h1 : ContinuousWithinAt riPhiEnv (Set.Icc 3 5) 5 := by
    refine ContinuousWithinAt.congr (f := fun s : ℝ => envNum s / s) henv
      (fun y hy => riPhiEnv_of_three_le hy.1) ?_
    exact riPhiEnv_of_three_le (by norm_num)
  have h2 : ContinuousWithinAt riPhiEnv (Set.Ici 5) 5 := by
    have henv' : ContinuousWithinAt (fun s : ℝ => envNum s / s) (Set.Ici 5) 5 :=
      (continuousWithinAt_envNum_ge_five le_rfl).div continuousWithinAt_id
        (by norm_num)
    refine ContinuousWithinAt.congr (f := fun s : ℝ => envNum s / s) henv'
      (fun y hy => riPhiEnv_of_three_le (by
        rw [Set.mem_Ici] at hy; linarith)) ?_
    exact riPhiEnv_of_three_le (by norm_num)
  have hu : ContinuousWithinAt riPhiEnv (Set.Ici 3) 5 :=
    (h1.union h2).mono (by
      intro y hy
      by_cases h5' : y ≤ 5
      · exact Or.inl ⟨hy, h5'⟩
      · exact Or.inr (le_of_lt (lt_of_not_ge h5')))
  exact hu.continuousAt (Ici_mem_nhds (by norm_num : (3:ℝ) < 5))

theorem continuousOn_riPhiEnv : ContinuousOn riPhiEnv (Set.Ioi 0) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  rcases lt_trichotomy x 3 with h3 | h3 | h3
  · exact (continuousAt_riPhiEnv_of_lt_three hx h3).continuousWithinAt
  · rw [h3]; exact continuousAt_riPhiEnv_three.continuousWithinAt
  · rcases lt_trichotomy x 5 with h5 | h5 | h5
    · exact (continuousAt_riPhiEnv_of_between h3 h5).continuousWithinAt
    · rw [h5]; exact continuousAt_riPhiEnv_five.continuousWithinAt
    · exact (continuousAt_riPhiEnv_of_gt_five h5).continuousWithinAt


end

end Work.NumberTheory.Chen.APSwitchUpper
