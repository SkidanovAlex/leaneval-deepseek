import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_double_pole
import Submission.Commons.Analysis.Complex.norm_cpow_gam_eq

namespace Commons.NumberTheory.Zeta

open Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval

noncomputable section

/-- `w ↦ c ^ w` is differentiable at every point when `c ≠ 0`. -/
lemma differentiableAt_cpow_const' {c w : ℂ} (hc : c ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => c ^ z) w :=
  (Complex.hasStrictDerivAt_const_cpow (Or.inl hc)).hasDerivAt.differentiableAt

/-- For `R ≥ 1` and `w.re ≤ 1`, `‖(R : ℂ) ^ w‖ ≤ R`. -/
lemma norm_cpow_le_of_re_le_one {R : ℝ} (hR : 1 ≤ R) {w : ℂ} (hw : w.re ≤ 1) :
    ‖(R : ℂ) ^ w‖ ≤ R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
  calc R ^ w.re ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hw
    _ = R := Real.rpow_one R

/-- For `R ≥ 1` and `w.re ≤ 0`, `‖(R : ℂ) ^ w‖ ≤ 1`. -/
lemma norm_cpow_le_one_of_re_nonpos {R : ℝ} (hR : 1 ≤ R) {w : ℂ} (hw : w.re ≤ 0) :
    ‖(R : ℂ) ^ w‖ ≤ 1 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
  exact Real.rpow_le_one_of_one_le_of_nonpos hR hw

/-- Norm of `(1 : ℂ) + t * I`. -/
lemma sq_norm_one_add_mul_I (t : ℝ) : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- Horizontal-segment integral of `h z / z^2` tends to `0` when `h` is bounded by `M` on the
strip `{-(β/log(|Im z|+2)) ≤ Re z ≤ c}`. -/
lemma horizontal_double_pole_tendsto {β c M : ℝ} (hβ : 0 < β) (hc : 0 < c) (hM : 0 ≤ M)
    (h : ℂ → ℂ)
    (hb : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → ‖h z‖ ≤ M) :
    Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
        - (∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2))
      Filter.atTop (nhds 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 2 * M * (c + β / Real.log 2) with hK
  have hbound : ∀ᶠ (T : ℝ) in Filter.atTop,
      ‖(∫ u in (-(β / Real.log (T + 2)))..c,
            h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
        - (∫ u in (-(β / Real.log (T + 2)))..c,
            h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)‖
        ≤ K * (T⁻¹) ^ 2 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hac : -(β / Real.log (T + 2)) ≤ c := by
      have : 0 < β / Real.log (T + 2) := div_pos hβ (Real.log_pos (by linarith))
      linarith
    have hlen : |c - (-(β / Real.log (T + 2)))| ≤ c + β / Real.log 2 := by
      have h1 : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith)
      have h2 : β / Real.log (T + 2) ≤ β / Real.log 2 :=
        div_le_div_of_nonneg_left hβ.le hlog2 h1
      have h3 : 0 < β / Real.log (T + 2) := div_pos hβ (Real.log_pos (by linarith))
      have h4 : c - (-(β / Real.log (T + 2))) = c + β / Real.log (T + 2) := by ring
      rw [h4, abs_of_pos (by linarith)]
      linarith
    have hpt : ∀ (s : ℝ), |s| = T → ∀ u ∈ Set.uIoc (-(β / Real.log (T + 2))) c,
        ‖h ((u : ℂ) + (s : ℂ) * Complex.I) / ((u : ℂ) + (s : ℂ) * Complex.I) ^ 2‖
          ≤ M * (T ^ 2)⁻¹ := by
      intro s hs u hu
      have hsT : s ^ 2 = T ^ 2 := by rw [← sq_abs, hs]
      have hsu : s ≠ 0 := by intro h0; rw [h0, abs_zero] at hs; linarith
      have him : ((u : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
      have hre' : ((u : ℂ) + (s : ℂ) * Complex.I).re = u := by simp
      have ha : -(β / Real.log (T + 2)) < u := by
        have hh := hu.1; rwa [min_eq_left hac] at hh
      have huc : u ≤ c := by
        have hh := hu.2; rwa [max_eq_right hac] at hh
      have hreg : -(β / Real.log (|((u : ℂ) + (s : ℂ) * Complex.I).im| + 2))
          ≤ ((u : ℂ) + (s : ℂ) * Complex.I).re := by
        rw [him, hre', hs]; exact ha.le
      have hbore : ‖h ((u : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M := hb _ hreg (by rw [hre']; exact huc)
      calc ‖h ((u : ℂ) + (s : ℂ) * Complex.I) / ((u : ℂ) + (s : ℂ) * Complex.I) ^ 2‖
          = ‖h ((u : ℂ) + (s : ℂ) * Complex.I)‖
              * ‖(((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹‖ := by
            rw [div_eq_mul_inv, norm_mul]
        _ ≤ M * (s ^ 2)⁻¹ :=
            mul_le_mul hbore (Commons.Analysis.Complex.norm_inv_sq_le hsu) (norm_nonneg _) hM
        _ = M * (T ^ 2)⁻¹ := by rw [hsT]
    have hb1 : ‖∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2‖
        ≤ M * (T ^ 2)⁻¹ * (c + β / Real.log 2) := by
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun u hu => hpt T (abs_of_pos hT) u hu)) ?_
      exact mul_le_mul_of_nonneg_left hlen (by positivity)
    have hI2 : (∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)
        = ∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) / ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ^ 2 := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hz : ((x : ℂ) - (T : ℂ) * Complex.I) = ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hz]
    have hb2 : ‖∫ u in (-(β / Real.log (T + 2)))..c,
          h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2‖
        ≤ M * (T ^ 2)⁻¹ * (c + β / Real.log 2) := by
      rw [hI2]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun u hu => hpt (-T) (by rw [abs_neg, abs_of_pos hT]) u hu)) ?_
      exact mul_le_mul_of_nonneg_left hlen (by positivity)
    calc ‖(∫ u in (-(β / Real.log (T + 2)))..c,
            h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
        - (∫ u in (-(β / Real.log (T + 2)))..c,
            h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2)‖
        ≤ M * (T ^ 2)⁻¹ * (c + β / Real.log 2) + M * (T ^ 2)⁻¹ * (c + β / Real.log 2) := by
          linarith [norm_sub_le (∫ u in (-(β / Real.log (T + 2)))..c,
              h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
            (∫ u in (-(β / Real.log (T + 2)))..c,
              h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2), hb1, hb2]
      _ = K * (T⁻¹) ^ 2 := by rw [hK, inv_pow]; ring
  have hlimK : Filter.Tendsto (fun T : ℝ => K * (T⁻¹) ^ 2) Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
    simpa using h.const_mul K
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hlimK)

/-- Contour shift for a double pole, assembled with `Γ₀` written using `gam`/`gamDot`. -/
lemma greenTao_G2_aux {β : ℝ} (hβ : 0 < β) (h : ℂ → ℂ) (B : ℝ)
    (hd : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 → DifferentiableAt ℂ h z)
    (hb : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 → ‖h z‖ ≤ B) :
    (∫ t : ℝ, h ((1 : ℂ) + (t : ℂ) * Complex.I) / ((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2
        * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I * deriv h 0
        + (∫ t : ℝ, h (Commons.Analysis.Complex.gam β t)
            / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBnonneg : 0 ≤ B := by
    have h0 : -(β / Real.log (|(0:ℂ).im| + 2)) ≤ (0:ℂ).re := by
      simp only [Complex.zero_re, Complex.zero_im, abs_zero, zero_add]
      have hpos : 0 < β / Real.log 2 := div_pos hβ hlog2
      linarith
    have h1 : (0:ℂ).re ≤ 1 := by simp
    exact le_trans (norm_nonneg _) (hb 0 h0 h1)
  have hline_reg : ∀ t : ℝ, -(β / Real.log (|((1:ℂ) + (t:ℂ)*Complex.I).im| + 2))
      ≤ ((1:ℂ) + (t:ℂ)*Complex.I).re := by
    intro t
    have him : ((1:ℂ) + (t:ℂ)*Complex.I).im = t := by simp
    have hre : ((1:ℂ) + (t:ℂ)*Complex.I).re = 1 := by simp
    rw [him, hre]
    have hlog : 0 < Real.log (|t| + 2) := Real.log_pos (by have := abs_nonneg t; linarith)
    have : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le hlog.le
    linarith
  have hline_le : ∀ t : ℝ, ((1:ℂ) + (t:ℂ)*Complex.I).re ≤ 1 := by
    intro t; simp
  have hgam_reg : ∀ t : ℝ, -(β / Real.log (|(Commons.Analysis.Complex.gam β t).im| + 2))
      ≤ (Commons.Analysis.Complex.gam β t).re := by
    intro t
    rw [Commons.Analysis.Complex.gam_im, Commons.Analysis.Complex.gam_re]
  have hgam_le : ∀ t : ℝ, (Commons.Analysis.Complex.gam β t).re ≤ 1 := by
    intro t
    rw [Commons.Analysis.Complex.gam_re]
    have hlog : 0 < Real.log (|t| + 2) := Real.log_pos (by have := abs_nonneg t; linarith)
    have : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le hlog.le
    linarith
  have hc_line : Continuous (fun t : ℝ => (1:ℂ) + (t:ℂ)*Complex.I) := by fun_prop
  have hhcont : Continuous (fun t : ℝ => h ((1:ℂ) + (t:ℂ)*Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (g := h) (f := fun t : ℝ => (1:ℂ) + (t:ℂ)*Complex.I) (x := t)
      ((hd _ (hline_reg t) (hline_le t)).continuousAt) hc_line.continuousAt
  have hhcont_gam : Continuous (fun t : ℝ => h (Commons.Analysis.Complex.gam β t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ((hd _ (hgam_reg t) (hgam_le t)).continuousAt.comp
      (Commons.Analysis.Complex.gam_continuous β).continuousAt)
  have hz_ne : ∀ t : ℝ, ((1:ℂ) + (t:ℂ)*Complex.I) ≠ 0 := by
    intro t hh
    have : ((1:ℂ) + (t:ℂ)*Complex.I).re = 0 := by rw [hh]; simp
    simp at this
  have hint1 : MeasureTheory.Integrable (fun t : ℝ =>
      h ((1:ℂ) + (t:ℂ)*Complex.I) / ((1:ℂ) + (t:ℂ)*Complex.I)^2 * Complex.I) := by
    have hcont : Continuous (fun t : ℝ =>
        h ((1:ℂ) + (t:ℂ)*Complex.I) / ((1:ℂ) + (t:ℂ)*Complex.I)^2 * Complex.I) :=
      (hhcont.div ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2)
        (fun t => pow_ne_zero 2 (hz_ne t))).mul continuous_const
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul B) hcont.aestronglyMeasurable ?_
    filter_upwards with t
    have hbnd : ‖h ((1:ℂ) + (t:ℂ)*Complex.I)‖ ≤ B := hb _ (hline_reg t) (hline_le t)
    calc ‖h ((1:ℂ) + (t:ℂ)*Complex.I) / ((1:ℂ) + (t:ℂ)*Complex.I)^2 * Complex.I‖
        = ‖h ((1:ℂ) + (t:ℂ)*Complex.I)‖ * (1 + t^2)⁻¹ := by
          simp only [div_eq_mul_inv, norm_mul, norm_inv, norm_pow, sq_norm_one_add_mul_I,
            Complex.norm_I, mul_one]
      _ ≤ B * (1 + t^2)⁻¹ := mul_le_mul_of_nonneg_right hbnd (by positivity)
  have hgam_cont : Continuous (fun t : ℝ => h (Commons.Analysis.Complex.gam β t)
      / (Commons.Analysis.Complex.gam β t)^2) :=
    hhcont_gam.div ((Commons.Analysis.Complex.gam_continuous β).pow 2)
      (fun t => pow_ne_zero 2 (Commons.Analysis.Complex.gam_ne_zero hβ t))
  have hgamDot_meas : AEStronglyMeasurable (fun t : ℝ => Commons.Analysis.Complex.gamDot β t)
      (volume : Measure ℝ) :=
    (aestronglyMeasurable_deriv (Commons.Analysis.Complex.gam β) volume).congr
      (by filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
          rw [(Commons.Analysis.Complex.hasDerivAt_gam (β := β) ht).deriv])
  have hint0_gam : MeasureTheory.Integrable (fun t : ℝ =>
      h (Commons.Analysis.Complex.gam β t) / (Commons.Analysis.Complex.gam β t)^2
        * Commons.Analysis.Complex.gamDot β t) := by
    refine Integrable.mono'
      (integrable_inv_one_add_sq.const_mul (B * Commons.Analysis.Complex.curveConst β))
      (hgam_cont.aestronglyMeasurable.mul hgamDot_meas) ?_
    filter_upwards with t
    have hbnd : ‖h (Commons.Analysis.Complex.gam β t)‖ ≤ B := hb _ (hgam_reg t) (hgam_le t)
    have h2 : ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t‖
        ≤ Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹ :=
      Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ t
    have hrw : h (Commons.Analysis.Complex.gam β t) / (Commons.Analysis.Complex.gam β t)^2
          * Commons.Analysis.Complex.gamDot β t
        = h (Commons.Analysis.Complex.gam β t)
          * (((Commons.Analysis.Complex.gam β t)^2)⁻¹ * Commons.Analysis.Complex.gamDot β t) := by
      rw [div_eq_mul_inv, mul_assoc]
    calc ‖h (Commons.Analysis.Complex.gam β t) / (Commons.Analysis.Complex.gam β t)^2
          * Commons.Analysis.Complex.gamDot β t‖
        = ‖h (Commons.Analysis.Complex.gam β t)‖
            * ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t‖ := by
          rw [hrw, norm_mul]
      _ ≤ B * (Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹) :=
          mul_le_mul hbnd h2 (norm_nonneg _) hBnonneg
      _ = (B * Commons.Analysis.Complex.curveConst β) * (1 + t^2)⁻¹ := by ring
  have hint0 : MeasureTheory.Integrable (fun t : ℝ =>
      h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) := by
    refine hint0_gam.congr ?_
    filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
    rw [Commons.Analysis.Complex.deriv_phi_curve (β := β) ht]
    simp only [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
  have hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..1,
          h ((u : ℂ) + (T : ℂ) * Complex.I) / ((u : ℂ) + (T : ℂ) * Complex.I) ^ 2)
        - (∫ u in (-(β / Real.log (T + 2)))..1,
          h ((u : ℂ) - (T : ℂ) * Complex.I) / ((u : ℂ) - (T : ℂ) * Complex.I) ^ 2))
      Filter.atTop (nhds 0) :=
    horizontal_double_pole_tendsto hβ (by norm_num) hBnonneg h hb
  have key := Commons.Analysis.Complex.contour_shift_double_pole (β := β) (c := 1) hβ (by norm_num) h hd hint1 hint0 hhoriz
  have hconv : (∫ t : ℝ, h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
      = ∫ t : ℝ, h (Commons.Analysis.Complex.gam β t)
          / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
    rw [Commons.Analysis.Complex.deriv_phi_curve (β := β) ht]
    simp only [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
  have key' : (∫ t : ℝ, h ((1 : ℂ) + (t : ℂ) * Complex.I) / ((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2
        * Complex.I)
      = (∫ t : ℝ, h (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / ((((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ^ 2
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        + 2 * (Real.pi : ℂ) * Complex.I * deriv h 0 := by
    simpa only [Complex.ofReal_one] using key
  rw [key', hconv]
  ring

/-- **Green–Tao, double pole at the origin of the `Γ₂` integrand.**

For `h : ℂ → ℂ` on the classical zero-free region, the contour integral of `h z / z²` over the
vertical line `Re z = 1` equals `2πi h'(0)` (the residue of the double pole at `0`) plus the same
integral over the boundary curve `Γ₀ = {Re z = -β/log(|Im z|+2)}`. -/
theorem greenTao_Gamma2_double_pole {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) (f : ℂ → ℂ → ℂ) (B : ℝ)
    (hd : ∀ z' : ℂ, -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f 0 u) z')
    (hb : ∀ z' : ℂ, -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f 0 z'‖ ≤ B) :
    (∫ t : ℝ, (f 0 ((1 : ℂ) + (t : ℂ) * Complex.I) * (R : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
        / ((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2 * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I * deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
        + (∫ t : ℝ, (f 0 (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
            / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t) := by
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBnonneg : 0 ≤ B := by
    have h0 : -(β / Real.log (|(0:ℂ).im| + 2)) ≤ (0:ℂ).re := by
      simp only [Complex.zero_re, Complex.zero_im, abs_zero, zero_add]
      have hpos : 0 < β / Real.log 2 := div_pos hβ hlog2
      linarith
    exact le_trans (norm_nonneg _) (hb 0 h0 (by simp))
  have hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      DifferentiableAt ℂ (fun w : ℂ => f 0 w * (R : ℂ) ^ w) z :=
    fun z h1 h2 => (hd z h1 h2).mul (differentiableAt_cpow_const' hRne)
  have hbnd : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      ‖f 0 z * (R : ℂ) ^ z‖ ≤ B * R := by
    intro z h1 h2
    rw [norm_mul]
    exact mul_le_mul (hb z h1 h2) (norm_cpow_le_of_re_le_one hR1 h2) (norm_nonneg _) hBnonneg
  exact greenTao_G2_aux (β := β) hβ (fun w : ℂ => f 0 w * (R : ℂ) ^ w) (B * R) hdiff hbnd

end

end Commons.NumberTheory.Zeta
