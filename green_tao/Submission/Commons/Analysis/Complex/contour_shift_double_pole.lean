import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable

namespace Commons.Analysis.Complex

/-!
# Contour shift for a DOUBLE pole at the origin

Companion of `Commons.Analysis.Complex.contour_shift_residue` (which handles a single SIMPLE pole at
`0`).  Here the integrand is `h z / z ^ 2` with `h` analytic on the closed region
`{-(β/log(|Im z|+2)) ≤ Re z ≤ c}`, and the pole at the origin is double.  Shifting the vertical line
`Re z = c` to the curve `Γ₀ = {Re = -β/log(|Im|+2)}` therefore picks up the residue `h'(0)`:

`(1/2πi) ∫_{Re = c} h z / z² dz  =  (1/2πi) ∫_{Γ₀} h z / z² dz + h'(0)`.

(Note the absence of the factor `2πi`: it is `2πi·h'(0)` divided by `2πi`.)

## Proof

Apply `Commons.Analysis.Complex.contour_shift_residue` with `c := c`, `r := deriv h 0` to the
function `g z := (h z - h 0) / z ^ 2`.  At `z = 0` the singularity is removable in `g·z`
(the Taylor expansion `h z - h 0 = h'(0) z + O(z²)`), hence `z * g z → h'(0)`.  Then subtract the
trivial identities `∫_{Re = c} dz/z² = 0` and `∫_{Γ₀} dz/z² = 0` (both integrands have the global
antiderivative `-1/z` on their contour, where `Re z ≠ 0`), multiplied by the constant `h 0`.

The horizontal-integral hypothesis for `g` follows from the one for `h`: the extra term is
`h 0 · ∫_{-β/log(T+2)}^{c} dz/z²` with `z = u ± iT`, which tends to `0` as `T → ∞`.
-/
open Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval


noncomputable section

/-! ## Auxiliary lemmas: vertical line `Re z = c` -/

lemma vert_ne_zero_of_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have : ((c : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
  simp at this
  linarith

lemma norm_vert_inv_sq (c t : ℝ) :
    ‖(((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I‖ = (c ^ 2 + t ^ 2)⁻¹ := by
  rw [norm_mul, norm_inv, norm_pow, Complex.sq_norm, Complex.norm_I, mul_one]
  simp [Complex.normSq_apply]
  ring

lemma vertical_inv_sq_integrable {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun t : ℝ => (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hmin : 0 < min (c ^ 2) 1 := lt_min hc2 one_pos
  have hcont : Continuous (fun t : ℝ => (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I) :=
    (((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2).inv₀
      (fun t => pow_ne_zero 2 (vert_ne_zero_of_pos hc t))).mul continuous_const
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul ((min (c ^ 2) 1)⁻¹))
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_vert_inv_sq]
  have hle : min (c ^ 2) 1 * (1 + t ^ 2) ≤ c ^ 2 + t ^ 2 := by
    rcases le_total (c^2) 1 with hh | hh
    · rw [min_eq_left hh]; nlinarith [sq_nonneg t, hh]
    · rw [min_eq_right hh]; nlinarith [sq_nonneg t, hh]
  have hpos1 : 0 < min (c ^ 2) 1 * (1 + t ^ 2) := mul_pos hmin (by positivity)
  have hpos2 : 0 < c ^ 2 + t ^ 2 := by positivity
  calc (c ^ 2 + t ^ 2)⁻¹ ≤ (min (c ^ 2) 1 * (1 + t ^ 2))⁻¹ := inv_anti₀ hpos1 hle
    _ = (min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := mul_inv _ _

lemma tendsto_inv_vert_atTop {c : ℝ} :
    Filter.Tendsto (fun t : ℝ => (((c : ℂ) + (t : ℂ) * Complex.I))⁻¹) Filter.atTop (nhds 0) := by
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖((c : ℂ) + (t : ℂ) * Complex.I)‖) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono (fun t => by simpa using Complex.abs_im_le_norm ((c : ℂ) + (t : ℂ) * Complex.I))
      tendsto_abs_atTop_atTop
  have h2 : Filter.Tendsto (fun t : ℝ => ‖((c : ℂ) + (t : ℂ) * Complex.I)‖⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have h1 : Filter.Tendsto (fun t : ℝ => ‖(((c : ℂ) + (t : ℂ) * Complex.I))⁻¹‖) Filter.atTop (nhds 0) := by
    simpa only [norm_inv] using h2
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h1

lemma tendsto_inv_vert_atBot {c : ℝ} :
    Filter.Tendsto (fun t : ℝ => (((c : ℂ) + (t : ℂ) * Complex.I))⁻¹) Filter.atBot (nhds 0) := by
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖((c : ℂ) + (t : ℂ) * Complex.I)‖) Filter.atBot Filter.atTop :=
    tendsto_atTop_mono (fun t => by simpa using Complex.abs_im_le_norm ((c : ℂ) + (t : ℂ) * Complex.I))
      tendsto_abs_atBot_atTop
  have h2 : Filter.Tendsto (fun t : ℝ => ‖((c : ℂ) + (t : ℂ) * Complex.I)‖⁻¹) Filter.atBot (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have h1 : Filter.Tendsto (fun t : ℝ => ‖(((c : ℂ) + (t : ℂ) * Complex.I))⁻¹‖) Filter.atBot (nhds 0) := by
    simpa only [norm_inv] using h2
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h1

lemma vertical_inv_sq_integral_zero {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I) = 0 := by
  have hint := vertical_inv_sq_integrable hc
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -(((c : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      ((((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I) t := by
    intro t
    have hz : HasDerivAt (fun s : ℝ => (c : ℂ) + (s : ℂ) * Complex.I) Complex.I t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).const_add (c : ℂ)
    have hinv := (hz.inv (vert_ne_zero_of_pos hc t)).neg
    refine hinv.congr_deriv ?_
    rw [div_eq_mul_inv]; ring
  have hbot : Filter.Tendsto (fun t : ℝ => -(((c : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      Filter.atBot (nhds 0) := by
    simpa using (tendsto_inv_vert_atBot (c := c)).neg
  have htop : Filter.Tendsto (fun t : ℝ => -(((c : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_vert_atTop (c := c)).neg
  have := integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop
  simpa using this

/-! ## Auxiliary lemmas: the boundary curve `gam` -/

lemma deriv_phi_curve {β : ℝ} {t : ℝ} (ht : t ≠ 0) :
    deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
      = gamDot β t := by
  have hfun : (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I))
      = gam β := by
    funext s; simp [gam, phi]
  rw [hfun, (hasDerivAt_gam (β := β) ht).deriv]

lemma curve_inv_sq_eq {β : ℝ} {t : ℝ} (ht : t ≠ 0) :
    (((( -(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹
        * deriv (fun s : ℝ => ((( -(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
      = (gam β t ^ 2)⁻¹ * gamDot β t := by
  rw [deriv_phi_curve (β := β) ht]
  have hfun : (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I))
      = gam β := by
    funext s; simp [gam, phi]
  rw [← hfun]

lemma tendsto_inv_gam_atTop {β : ℝ} :
    Filter.Tendsto (fun t : ℝ => (gam β t)⁻¹) Filter.atTop (nhds 0) := by
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖gam β t‖) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono (fun t => Commons.Analysis.Integral.gam_norm_ge_abs β t)
      tendsto_abs_atTop_atTop
  have h2 : Filter.Tendsto (fun t : ℝ => ‖gam β t‖⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [norm_inv] using h2)

lemma tendsto_inv_gam_atBot {β : ℝ} :
    Filter.Tendsto (fun t : ℝ => (gam β t)⁻¹) Filter.atBot (nhds 0) := by
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖gam β t‖) Filter.atBot Filter.atTop :=
    tendsto_atTop_mono (fun t => Commons.Analysis.Integral.gam_norm_ge_abs β t)
      tendsto_abs_atBot_atTop
  have h2 : Filter.Tendsto (fun t : ℝ => ‖gam β t‖⁻¹) Filter.atBot (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [norm_inv] using h2)

lemma hasDerivAt_neg_inv_gam {β : ℝ} (hβ : 0 < β) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -((gam β y)⁻¹)) ((gam β x ^ 2)⁻¹ * gamDot β x) x := by
  have hb := (hasDerivAt_gam (β := β) hx).inv (gam_ne_zero hβ x)
  have hneg := hb.neg
  refine hneg.congr_deriv ?_
  rw [div_eq_mul_inv]; ring

lemma curve_inv_sq_integral_zero {β : ℝ} (hβ : 0 < β) :
    (∫ t : ℝ,
      (((( -(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹
        * deriv (fun s : ℝ => ((( -(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) = 0 := by
  have hintF := curve_inv_sq_integrable (β := β) hβ
  have hintG : Integrable (fun t : ℝ => (gam β t ^ 2)⁻¹ * gamDot β t) :=
    hintF.congr (by
      filter_upwards [ae_ne_zero] with t ht
      exact curve_inv_sq_eq (β := β) ht)
  have hval : ∀ᶠ T in Filter.atTop,
      (∫ y in (-T)..T, (gam β y ^ 2)⁻¹ * gamDot β y) = -((gam β T)⁻¹) + ((gam β (-T))⁻¹) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hcont1 : ContinuousOn (fun y : ℝ => -((gam β y)⁻¹)) (Set.Icc (0:ℝ) T) :=
      (ContinuousOn.inv₀ ((gam_continuous β).continuousOn) (fun x hx => gam_ne_zero hβ x)).neg
    have h1 : (∫ y in (0:ℝ)..T, (gam β y ^ 2)⁻¹ * gamDot β y) = -((gam β T)⁻¹) + ((gam β 0)⁻¹) := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := T)
        (f := fun y : ℝ => -((gam β y)⁻¹))
        (f' := fun y : ℝ => (gam β y ^ 2)⁻¹ * gamDot β y) hT.le hcont1
        (fun x hx => hasDerivAt_neg_inv_gam hβ (ne_of_gt hx.1)) hintG.intervalIntegrable
      simpa using this
    have hcont2 : ContinuousOn (fun y : ℝ => -((gam β y)⁻¹)) (Set.Icc (-T) (0:ℝ)) :=
      (ContinuousOn.inv₀ ((gam_continuous β).continuousOn) (fun x hx => gam_ne_zero hβ x)).neg
    have h2 : (∫ y in (-T)..0, (gam β y ^ 2)⁻¹ * gamDot β y) = -((gam β 0)⁻¹) + ((gam β (-T))⁻¹) := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := -T) (b := 0)
        (f := fun y : ℝ => -((gam β y)⁻¹))
        (f' := fun y : ℝ => (gam β y ^ 2)⁻¹ * gamDot β y) (by linarith : -T ≤ 0) hcont2
        (fun x hx => hasDerivAt_neg_inv_gam hβ (ne_of_lt hx.2)) hintG.intervalIntegrable
      simpa using this
    rw [← intervalIntegral.integral_add_adjacent_intervals hintG.intervalIntegrable
      hintG.intervalIntegrable, h1, h2]
    ring
  have hlim : Tendsto (fun T : ℝ => (∫ y in (-T)..T, (gam β y ^ 2)⁻¹ * gamDot β y))
      Filter.atTop (nhds (∫ y : ℝ, (gam β y ^ 2)⁻¹ * gamDot β y)) :=
    intervalIntegral_tendsto_integral hintG tendsto_neg_atTop_atBot tendsto_id
  have hlim2 : Tendsto (fun T : ℝ => -((gam β T)⁻¹) + ((gam β (-T))⁻¹)) Filter.atTop (nhds 0) := by
    have ha : Tendsto (fun T : ℝ => -((gam β T)⁻¹)) Filter.atTop (nhds 0) := by
      simpa using (tendsto_inv_gam_atTop (β := β)).neg
    have hb : Tendsto (fun T : ℝ => ((gam β (-T))⁻¹)) Filter.atTop (nhds 0) :=
      (tendsto_inv_gam_atBot (β := β)).comp tendsto_neg_atTop_atBot
    simpa using ha.add hb
  have hzero : (∫ y : ℝ, (gam β y ^ 2)⁻¹ * gamDot β y) = 0 :=
    tendsto_nhds_unique (hlim.congr' hval) hlim2
  rw [← hzero]
  exact MeasureTheory.integral_congr_ae (by
    filter_upwards [ae_ne_zero] with t ht
    exact curve_inv_sq_eq (β := β) ht)

/-! ## Auxiliary lemmas: the horizontal segments -/

lemma norm_inv_sq_le {s u : ℝ} (hs : s ≠ 0) :
    ‖(((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹‖ ≤ (s ^ 2)⁻¹ := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hpos : 0 < u * u + s * s := by nlinarith [sq_nonneg u, hs2]
  rw [norm_inv, norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.ofReal_im, mul_one, add_zero,
    zero_add]
  rw [inv_le_inv₀ hpos hs2]
  nlinarith [sq_nonneg u]

lemma horizontal_inv_sq_tendsto {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹)
        - (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹))
      Filter.atTop (nhds 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 2 * (c + β / Real.log 2) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have : 0 < β / Real.log 2 := div_pos hβ hlog2
    linarith
  have hbound : ∀ᶠ (T : ℝ) in Filter.atTop,
      ‖(∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹)
        - (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹)‖
        ≤ K * (T⁻¹) ^ 2 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hlen : |c - (-(β / Real.log (T + 2)))| ≤ c + β / Real.log 2 := by
      have h1 : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith)
      have h2 : β / Real.log (T + 2) ≤ β / Real.log 2 :=
        div_le_div_of_nonneg_left hβ.le hlog2 h1
      have h3 : 0 < β / Real.log (T + 2) := div_pos hβ (Real.log_pos (by linarith))
      have h4 : c - (-(β / Real.log (T + 2))) = c + β / Real.log (T + 2) := by ring
      rw [h4, abs_of_pos (by linarith)]
      linarith
    have hI2 : (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹)
        = ∫ u in (-(β / Real.log (T + 2)))..c,
            (((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ^ 2)⁻¹ := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have : ((x : ℂ) - (T : ℂ) * Complex.I) = ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this]
    have hb1 : ‖∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹‖
        ≤ (T ^ 2)⁻¹ * |c - (-(β / Real.log (T + 2)))| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => norm_inv_sq_le (ne_of_gt hT))
    have hb2 : ‖∫ u in (-(β / Real.log (T + 2)))..c,
          (((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ^ 2)⁻¹‖
        ≤ (T ^ 2)⁻¹ * |c - (-(β / Real.log (T + 2)))| := by
      have hneg : ((-T : ℝ) ≠ 0) := by linarith
      have hT2 : ((-T) ^ 2)⁻¹ = (T ^ 2)⁻¹ := by ring_nf
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -(β / Real.log (T + 2))) (b := c) (C := ((-T : ℝ) ^ 2)⁻¹)
        (f := fun u : ℝ => (((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ^ 2)⁻¹)
        (fun x hx => norm_inv_sq_le hneg)
      rwa [hT2] at h
    have h2 : ‖∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹‖
        ≤ (T ^ 2)⁻¹ * |c - (-(β / Real.log (T + 2)))| := by
      rw [hI2]; exact hb2
    have hnn : 0 ≤ (T ^ 2)⁻¹ := by positivity
    calc ‖(∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹)
          - (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹)‖
        ≤ ‖∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹‖
          + ‖∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹‖ :=
          norm_sub_le _ _
      _ ≤ (T ^ 2)⁻¹ * (c + β / Real.log 2) + (T ^ 2)⁻¹ * (c + β / Real.log 2) := by
          have ha := mul_le_mul_of_nonneg_left hlen hnn
          linarith
      _ = K * (T⁻¹) ^ 2 := by
          rw [hK, inv_pow]; ring
  have hlimK : Filter.Tendsto (fun T : ℝ => K * (T⁻¹) ^ 2) Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
    simpa using h.const_mul K
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hlimK)

/-! ## Continuity and interval integrability on the horizontal segments -/

lemma horizontal_ne_zero (x s : ℝ) (hs : s ≠ 0) : ((x : ℂ) + (s : ℂ) * Complex.I) ≠ 0 := by
  intro hh
  have him : ((x : ℂ) + (s : ℂ) * Complex.I).im = 0 := by rw [hh]; simp
  simp at him
  exact hs him

lemma continuousOn_horiz_h_div {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {h : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → DifferentiableAt ℂ h z)
    {s : ℝ} (hs : s ≠ 0) :
    ContinuousOn (fun u : ℝ => h ((u : ℂ) + (s : ℂ) * Complex.I) / ((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)
      (Set.Icc (phi β s) c) := by
  refine ContinuousOn.div ?_ (by fun_prop) ?_
  · exact continuousOn_g_horiz hβ hc (fun z h1 h2 _ => hdiff z h1 h2) hs
  · intro u hu
    exact pow_ne_zero 2 (horizontal_ne_zero u s hs)

lemma continuousOn_horiz_inv_sq {β c : ℝ} {s : ℝ} (hs : s ≠ 0) :
    ContinuousOn (fun u : ℝ => (((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹) (Set.Icc (phi β s) c) := by
  refine ContinuousOn.inv₀ (by fun_prop) ?_
  intro u hu
  exact pow_ne_zero 2 (horizontal_ne_zero u s hs)

lemma intervalIntegrable_of_continuousOn_horiz {g : ℂ → ℂ} {s A c : ℝ} (hAc : A ≤ c)
    (hcont : ContinuousOn (fun u : ℝ => g ((u : ℂ) + (s : ℂ) * Complex.I)) (Set.Icc A c)) :
    IntervalIntegrable (fun u : ℝ => g ((u : ℂ) + (s : ℂ) * Complex.I)) volume A c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hAc]
  exact hcont



end

/-- Contour shift for a double pole at the origin. -/
theorem contour_shift_double_pole {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (h : ℂ → ℂ)
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → DifferentiableAt ℂ h z)
    (hint1 : MeasureTheory.Integrable (fun t : ℝ =>
      h ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2 * Complex.I))
    (hint0 : MeasureTheory.Integrable (fun t : ℝ =>
      h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t))
    (hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
        - (∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2))
      Filter.atTop (nhds 0)) :
    (∫ t : ℝ, h ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2
        * Complex.I)
      = (∫ t : ℝ, h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        + 2 * Real.pi * Complex.I * deriv h 0 := by
  have hdiffG : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ (fun z : ℂ => (h z - h 0) / z ^ 2) z := by
    intro z h1 h2 hz0
    exact ((hdiff z h1 h2).sub_const (h 0)).div (by fun_prop) (pow_ne_zero 2 hz0)
  have hresG : Filter.Tendsto (fun z : ℂ => z * ((h z - h 0) / z ^ 2))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (deriv h 0)) := by
    have hle0 : -(β / Real.log (|(0 : ℂ).im| + 2)) ≤ (0 : ℂ).re := by
      simp only [Complex.zero_re, Complex.zero_im, abs_zero, zero_add]
      have hlt : 0 < β / Real.log 2 := div_pos hβ (Real.log_pos (by norm_num))
      linarith
    have h0deriv : HasDerivAt h (deriv h 0) 0 :=
      (hdiff 0 hle0 (by simpa using hc.le)).hasDerivAt
    refine h0deriv.tendsto_slope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    rw [slope_def_field, sub_zero, div_eq_mul_inv, div_eq_mul_inv]
    field_simp
  have hpt_vert : ∀ t : ℝ,
      h ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2 * Complex.I
        = ((h ((c : ℂ) + (t : ℂ) * Complex.I) - h 0) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I
          + h 0 * ((((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I) := by
    intro t
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hverZ : MeasureTheory.Integrable
      (fun t : ℝ => ((((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I)) :=
    vertical_inv_sq_integrable hc
  have hverZ0 : (∫ t : ℝ, ((((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I)) = 0 :=
    vertical_inv_sq_integral_zero hc
  have hint1G : MeasureTheory.Integrable (fun t : ℝ =>
      ((h ((c : ℂ) + (t : ℂ) * Complex.I) - h 0) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)
        * Complex.I) := by
    refine (hint1.sub (hverZ.const_mul (h 0))).congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply]
    rw [hpt_vert t]
    ring
  have hcurZ : MeasureTheory.Integrable (fun t : ℝ =>
      (((( -(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹
        * deriv (fun s : ℝ => ((( -(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) :=
    curve_inv_sq_integrable hβ
  have hcurZ0 : (∫ t : ℝ,
      (((( -(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹
        * deriv (fun s : ℝ => ((( -(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) = 0 :=
    curve_inv_sq_integral_zero hβ
  have hpt_curve : ∀ t : ℝ,
      h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
        = ((h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) - h 0)
            / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2)
            * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
          + h 0 * ((((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2)⁻¹
            * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) := by
    intro t
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hint0G : MeasureTheory.Integrable (fun t : ℝ =>
      ((h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) - h 0)
        / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2)
        * deriv (fun s : ℝ => ((( -(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) := by
    refine (hint0.sub (hcurZ.const_mul (h 0))).congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply]
    rw [hpt_curve t]
    ring
  have hhorizZ : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹)
        - (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹))
      Filter.atTop (nhds 0) := horizontal_inv_sq_tendsto hβ hc
  have hhorizG : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c,
          (h ((u : ℂ) + (T : ℂ) * Complex.I) - h 0) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
        - (∫ u in (-(β / Real.log (T + 2)))..c,
          (h ((u : ℂ) - (T : ℂ) * Complex.I) - h 0) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2))
      Filter.atTop (nhds 0) := by
    have hcomb : Filter.Tendsto (fun T : ℝ =>
        ((∫ u in (-(β / Real.log (T + 2)))..c,
            h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
          - (∫ u in (-(β / Real.log (T + 2)))..c,
            h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2))
        - h 0 * ((∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)⁻¹)
          - (∫ u in (-(β / Real.log (T + 2)))..c, (((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)⁻¹)))
        Filter.atTop (nhds 0) := by
      have h := hhoriz.sub (hhorizZ.const_mul (h 0))
      simpa using h
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hsplit : ∀ s : ℝ, |s| = T →
        (∫ u in (-(β / Real.log (T + 2)))..c,
            (h ((u : ℂ) + (s : ℂ) * Complex.I) - h 0) / ((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)
          = (∫ u in (-(β / Real.log (T + 2)))..c,
              h ((u : ℂ) + (s : ℂ) * Complex.I) / ((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)
            - h 0 * (∫ u in (-(β / Real.log (T + 2)))..c,
                (((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹) := by
      intro s habs
      have hAs : (phi β s : ℝ) = -(β / Real.log (T + 2)) := by
        simp only [phi, habs]
      have hs : s ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at habs
        linarith
      have hIh : IntervalIntegrable (fun u : ℝ =>
          h ((u : ℂ) + (s : ℂ) * Complex.I) / ((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)
          volume (-(β / Real.log (T + 2))) c := by
        rw [← hAs]
        exact intervalIntegrable_of_continuousOn_horiz (g := fun z => h z / z ^ 2) (s := s)
          (le_of_lt (phi_lt_c hβ hc s)) (continuousOn_horiz_h_div hβ hc hdiff hs)
      have hIz : IntervalIntegrable (fun u : ℝ => (((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹)
          volume (-(β / Real.log (T + 2))) c := by
        rw [← hAs]
        exact intervalIntegrable_of_continuousOn_horiz (g := fun z => (z ^ 2)⁻¹) (s := s)
          (le_of_lt (phi_lt_c hβ hc s)) (continuousOn_horiz_inv_sq hs)
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hIh (hIz.const_mul (h 0))]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    have hconv : ∀ F : ℂ → ℂ,
        (∫ u in (-(β / Real.log (T + 2)))..c, F ((u : ℂ) - (T : ℂ) * Complex.I))
          = ∫ u in (-(β / Real.log (T + 2)))..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
      intro F
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      have hz : ((u : ℂ) - (T : ℂ) * Complex.I) = ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hz]
    have e1 := hsplit T (abs_of_pos hT)
    have e2 := hsplit (-T) (by rw [abs_neg, abs_of_pos hT])
    rw [hconv (fun z => (h z - h 0) / z ^ 2), hconv (fun z => h z / z ^ 2),
      hconv (fun z => (z ^ 2)⁻¹), e2, e1]
    ring
  have hcs := contour_shift_residue (β := β) (c := c) hβ hc
    (fun z : ℂ => (h z - h 0) / z ^ 2) (deriv h 0) hdiffG hresG hint1G hint0G hhorizG
  have hB : (∫ t : ℝ, h ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2
        * Complex.I)
      = ∫ t : ℝ, ((h ((c : ℂ) + (t : ℂ) * Complex.I) - h 0)
          / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I := by
    have h1 : (∫ t : ℝ, h ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2
          * Complex.I)
        = ∫ t : ℝ, (((h ((c : ℂ) + (t : ℂ) * Complex.I) - h 0)
              / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I
            + h 0 * ((((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹ * Complex.I)) :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall hpt_vert)
    rw [h1, MeasureTheory.integral_add hint1G (hverZ.const_mul (h 0)),
      MeasureTheory.integral_const_mul, hverZ0, mul_zero, add_zero]
  have hC : (∫ t : ℝ, h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
      = ∫ t : ℝ, ((h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) - h 0)
            / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2)
            * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t := by
    have h1 : (∫ t : ℝ, h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
            * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        = ∫ t : ℝ, (((h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) - h 0)
              / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2)
              * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
            + h 0 * ((((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2)⁻¹
              * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)) :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall hpt_curve)
    rw [h1, MeasureTheory.integral_add hint0G (hcurZ.const_mul (h 0)),
      MeasureTheory.integral_const_mul, hcurZ0, mul_zero, add_zero]
  rw [hB, hC]
  exact hcs

end Commons.Analysis.Complex
