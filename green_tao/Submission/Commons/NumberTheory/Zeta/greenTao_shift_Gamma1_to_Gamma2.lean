import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Submission.Commons.Analysis.Complex.vertical_shift_analytic
import Submission.Commons.Analysis.Integral.integrable_of_log_le_lorentz
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_const_of_one_lt_re

namespace Commons.NumberTheory.Zeta

open MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval

noncomputable section

/-- `1 < log 3`. -/
private lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three

/-- `(log (T+2) + 1) / T^2 → 0` as `T → ∞`. -/
private lemma tendsto_log_add_two_div_sq :
    Filter.Tendsto (fun T : ℝ => (Real.log (T + 2) + 1) / T ^ 2) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun T : ℝ => T + 2) Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hlog : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2)) Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun x : ℝ => Real.log x / (1 * x + 0)) Filter.atTop (nhds 0) :=
      by simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    refine (hbase.comp hshift).congr' ?_
    filter_upwards with T
    simp
  have hinv : Filter.Tendsto (fun T : ℝ => (1 : ℝ) / (T + 2)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hshift
  have hbase : Filter.Tendsto (fun T : ℝ => (Real.log (T + 2) + 1) / (T + 2)) Filter.atTop (nhds 0) := by
    have h := hlog.add hinv
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards with T
    exact (add_div (Real.log (T + 2)) 1 (T + 2)).symm
  refine squeeze_zero' ?_ ?_ hbase
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hlog : 0 ≤ Real.log (T + 2) + 1 := by
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    linarith
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hlog
  rw [inv_le_inv₀ (by positivity : (0 : ℝ) < T ^ 2) (by linarith : (0 : ℝ) < T + 2)]
  nlinarith

/-- **Vertical contour shift for `H w / w²` with logarithmic growth.**

If `H` is holomorphic on the strip `a ≤ Re w ≤ b` (`0 < a ≤ b`) and satisfies
`‖H w‖ ≤ C (log (|Im w| + 2) + 1)` there, then the vertical-line integrals of `H w / w² · i dz`
agree on `Re = a` and `Re = b`: there is no pole in the strip (`w = 0` lies to the left of `a`). -/
theorem vertical_shift_inv_sq_of_log_growth {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (H : ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → DifferentiableAt ℂ H w)
    (hgrowth : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖H w‖ ≤ C * (Real.log (|w.im| + 2) + 1)) :
    (∫ t : ℝ, H ((a : ℂ) + (t : ℂ) * Complex.I) / (((a : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I)
      = ∫ t : ℝ, H ((b : ℂ) + (t : ℂ) * Complex.I) / (((b : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I := by
  have hdiff_g : ∀ w : ℂ, a ≤ w.re → w.re ≤ b →
      DifferentiableAt ℂ (fun w : ℂ => H w / w ^ 2) w := by
    intro w h1 h2
    have hw : w ≠ 0 := by
      intro h; have : w.re = 0 := by rw [h]; simp
      linarith
    have hd := (hdiff w h1 h2).div (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => x ^ 2) w)
      (pow_ne_zero 2 hw)
    have hfun : (H / (fun x : ℂ => x ^ 2)) = (fun x : ℂ => H x / x ^ 2) := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at hd
    exact hd
  -- integrability of `H w · (w^2)^{-1}` on a vertical line `Re = σ`, `a ≤ σ ≤ b`
  have hline_int : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      Integrable (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ((((σ : ℂ) + (t : ℂ) * Complex.I)) ^ 2)⁻¹) := by
    intro σ hσ1 hσ2
    have hσpos : 0 < σ := lt_of_lt_of_le ha hσ1
    refine Commons.Analysis.Integral.integrable_of_log_le_lorentz
      (g := fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * Complex.I))
      (P := fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹)
      (K := 1) (b := 0) hσpos hC (by norm_num) ?_ ?_ ?_
    · have hcontH : Continuous (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [continuous_iff_continuousAt]; intro t
        have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
        exact ContinuousAt.comp (g := H) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
          (x := t) (hdiff _ (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)).continuousAt
          (by fun_prop)
      have hcontP : Continuous (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹) := by
        refine Continuous.inv₀ ?_ ?_
        · fun_prop
        · intro t
          apply pow_ne_zero
          intro h
          have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one] at this
          linarith
      exact (hcontH.mul hcontP).aestronglyMeasurable
    · intro t
      have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      have hthis := hgrowth ((σ : ℂ) + (t : ℂ) * Complex.I)
        (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
      rw [show ((σ : ℂ) + (t : ℂ) * Complex.I).im = t by simp] at hthis
      have hlog' : Real.log (|t| + 2) + 1 = Real.log (2 + |t|) + 1 := by rw [add_comm (|t|) 2]
      rw [hlog'] at hthis
      exact hthis
    · intro t
      have hsq : ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) ^ 2‖ = σ ^ 2 + t ^ 2 := by
        rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      rw [norm_inv, hsq, sub_zero, one_div]
  have hinta : Integrable (fun t : ℝ =>
      (fun w : ℂ => H w / w ^ 2) ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I) := by
    refine (hline_int a le_rfl hab).mul_const Complex.I |>.congr ?_
    filter_upwards with t
    simp only [div_eq_mul_inv]
  have hintb : Integrable (fun t : ℝ =>
      (fun w : ℂ => H w / w ^ 2) ((b : ℂ) + (t : ℂ) * Complex.I) * Complex.I) := by
    refine (hline_int b hab le_rfl).mul_const Complex.I |>.congr ?_
    filter_upwards with t
    simp only [div_eq_mul_inv]
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) - (T : ℂ) * Complex.I)))
      Filter.atTop (nhds 0) := by
    have hbnd : ∀ᶠ T : ℝ in Filter.atTop,
        ‖(∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (T : ℂ) * Complex.I))
          - (∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) - (T : ℂ) * Complex.I))‖
          ≤ (2 * (b - a) * C) * ((Real.log (T + 2) + 1) / T ^ 2) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hptT : ∀ s : ℝ, |s| = T → ∀ u ∈ Set.uIoc a b,
          ‖(fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (s : ℂ) * Complex.I)‖
            ≤ C * (Real.log (T + 2) + 1) * (T ^ 2)⁻¹ := by
        intro s hs u hu
        have hu1 : a < u := by have hh := hu.1; rwa [min_eq_left hab] at hh
        have hu2 : u ≤ b := by have hh := hu.2; rwa [max_eq_right hab] at hh
        have hre : ((u : ℂ) + (s : ℂ) * Complex.I).re = u := by simp
        have him : ((u : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
        have hs0 : s ≠ 0 := by intro h; rw [h, abs_zero] at hs; linarith
        have hHu : ‖H ((u : ℂ) + (s : ℂ) * Complex.I)‖ ≤ C * (Real.log (T + 2) + 1) := by
          have hthis := hgrowth ((u : ℂ) + (s : ℂ) * Complex.I)
            (by rw [hre]; exact hu1.le) (by rw [hre]; exact hu2)
          rw [him, hs] at hthis
          exact hthis
        have hden : ‖(((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹‖ ≤ (T ^ 2)⁻¹ := by
          rw [norm_inv]
          have hsq : ‖((u : ℂ) + (s : ℂ) * Complex.I) ^ 2‖ = u ^ 2 + s ^ 2 := by
            rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
            simp
            ring
          rw [hsq, inv_le_inv₀ (by nlinarith [sq_nonneg u, sq_pos_of_ne_zero hs0]) (pow_pos hT 2)]
          have hTs : T ^ 2 = s ^ 2 := by rw [← hs, sq_abs]
          rw [hTs]; nlinarith [sq_nonneg u]
        have hCpos : 0 ≤ C * (Real.log (T + 2) + 1) :=
          mul_nonneg hC (by have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith)
        calc ‖(fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (s : ℂ) * Complex.I)‖
            = ‖H ((u : ℂ) + (s : ℂ) * Complex.I)‖
              * ‖(((u : ℂ) + (s : ℂ) * Complex.I) ^ 2)⁻¹‖ := by
              simp only [div_eq_mul_inv, norm_mul]
          _ ≤ (C * (Real.log (T + 2) + 1)) * (T ^ 2)⁻¹ :=
              mul_le_mul hHu hden (norm_nonneg _) hCpos
          _ = C * (Real.log (T + 2) + 1) * (T ^ 2)⁻¹ := by ring
      have hlen : |b - a| = b - a := abs_of_nonneg hba
      have hb1 : ‖∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (T : ℂ) * Complex.I)‖
          ≤ (C * (Real.log (T + 2) + 1) * (T ^ 2)⁻¹) * (b - a) := by
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
          (fun u hu => hptT T (abs_of_pos hT) u hu)) ?_
        rw [hlen]
      have hb2 : ‖∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) - (T : ℂ) * Complex.I)‖
          ≤ (C * (Real.log (T + 2) + 1) * (T ^ 2)⁻¹) * (b - a) := by
        have hI : (∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) - (T : ℂ) * Complex.I))
            = ∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          congr 1; push_cast; ring
        rw [hI]
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
          (fun u hu => hptT (-T) (by rw [abs_neg, abs_of_pos hT]) u hu)) ?_
        rw [hlen]
      calc ‖(∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (T : ℂ) * Complex.I))
            - (∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) - (T : ℂ) * Complex.I))‖
          ≤ ‖∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) + (T : ℂ) * Complex.I)‖
            + ‖∫ u in a..b, (fun w : ℂ => H w / w ^ 2) ((u : ℂ) - (T : ℂ) * Complex.I)‖ :=
            norm_sub_le _ _
        _ ≤ (C * (Real.log (T + 2) + 1) * (T ^ 2)⁻¹) * (b - a)
            + (C * (Real.log (T + 2) + 1) * (T ^ 2)⁻¹) * (b - a) := add_le_add hb1 hb2
        _ = (2 * (b - a) * C) * ((Real.log (T + 2) + 1) / T ^ 2) := by
            rw [div_eq_mul_inv]; ring
    have hlim : Filter.Tendsto (fun T : ℝ => (2 * (b - a) * C)
        * ((Real.log (T + 2) + 1) / T ^ 2)) Filter.atTop (nhds 0) := by
      simpa using tendsto_log_add_two_div_sq.const_mul (2 * (b - a) * C)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbnd hlim)
  exact (Commons.Analysis.Complex.vertical_shift_analytic ha hab (fun w : ℂ => H w / w ^ 2)
    hdiff_g hinta hintb hhoriz).symm

/-- **Green–Tao, shift from `Γ₁` (`Re = 1/log R`) to `Γ₂` (`Re = 1`).**

Both vertical-line integrals of the Green–Tao integrand
`f z w · ζ(1+z+w)/(ζ(1+z) ζ(1+w)) · R^{z+w} / (z² w²) · i dw` agree: there is no pole in the
strip between `Re w = 1/log R` and `Re w = 1` (`w = 0` and `w = -z` both lie to the left). -/
theorem greenTao_shift_Gamma1_to_Gamma2 {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ : ℝ) (hC1 : 0 < C₁)
    (hinv : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hdiff2 : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z')
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    {z : ℂ} (hzre : z.re = 1 / Real.log R) (hzreg : -(β / Real.log (|z.im| + 2)) ≤ z.re) :
    (∫ t : ℝ, (fun w : ℂ => f z w
        * (riemannZeta (1 + z + w) / (riemannZeta (1 + z) * riemannZeta (1 + w)))
        * (R : ℂ) ^ (z + w) / (z ^ 2 * w ^ 2))
        (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = (∫ t : ℝ, (fun w : ℂ => f z w
        * (riemannZeta (1 + z + w) / (riemannZeta (1 + z) * riemannZeta (1 + w)))
        * (R : ℂ) ^ (z + w) / (z ^ 2 * w ^ 2))
        ((1 : ℂ) + (t : ℂ) * Complex.I) * Complex.I) := by
  set a : ℝ := 1 / Real.log R with ha_def
  have hRpos : 0 < R := by linarith
  have hlogRpos : 0 < Real.log R := Real.log_pos (by linarith)
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le_one : a ≤ 1 := by
    rw [ha_def]
    have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hle : Real.log 3 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    have h1 : (1:ℝ)/Real.log R ≤ 1/Real.log 3 := one_div_le_one_div_of_le hlog3pos hle
    have h2 : (1:ℝ)/Real.log 3 ≤ 1 := by rw [div_le_one hlog3pos]; linarith [one_lt_log_three]
    linarith
  have hzre' : z.re = a := by rw [ha_def]; exact hzre
  have hzle : z.re ≤ 1 := by rw [hzre']; exact ha_le_one
  have hz_ne : z ≠ 0 := by
    intro h; have : z.re = 0 := by rw [h]; simp
    rw [hzre'] at this; linarith
  obtain ⟨Cζ, hCζpos, hCζ⟩ := norm_riemannZeta_le_const_of_one_lt_re (σ := 1 + a) (by linarith)
  have hBnn : 0 ≤ B := by
    have h0reg : -(β / Real.log (|(0:ℂ).im| + 2)) ≤ (0:ℂ).re := by
      simp only [Complex.zero_re, Complex.zero_im, abs_zero, zero_add]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have : 0 ≤ β / Real.log 2 := div_nonneg hβ.le hlog2.le
      linarith
    have h0le : (0:ℂ).re ≤ 1 := by simp
    exact le_trans (norm_nonneg _) (hbound z 0 hzreg hzle h0reg h0le)
  let Hfun : ℂ → ℂ := fun w => f z w * riemannZeta (1 + z + w) * (riemannZeta (1 + w))⁻¹
    * (R : ℂ) ^ (z + w)
  let K : ℂ := (riemannZeta (1 + z) * z ^ 2)⁻¹
  let Ffun : ℂ → ℂ := fun w => f z w
    * (riemannZeta (1 + z + w) / (riemannZeta (1 + z) * riemannZeta (1 + w)))
    * (R : ℂ) ^ (z + w) / (z ^ 2 * w ^ 2)
  have hdiff_H : ∀ w : ℂ, a ≤ w.re → w.re ≤ 1 → DifferentiableAt ℂ Hfun w := by
    intro w hw1 hw2
    change DifferentiableAt ℂ (fun w : ℂ => f z w * riemannZeta (1 + z + w)
      * (riemannZeta (1 + w))⁻¹ * (R : ℂ) ^ (z + w)) w
    have hregw : -(β / Real.log (|w.im| + 2)) ≤ w.re := by
      have : 0 ≤ β / Real.log (|w.im| + 2) :=
        div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg w.im]))
      linarith
    have hf : DifferentiableAt ℂ (fun u : ℂ => f z u) w := hdiff2 z w hzreg hzle hregw hw2
    have hne1 : (1 : ℂ) + z + w ≠ 1 := by
      intro h; have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, hzre'] at hr
      linarith [hw1, ha_pos]
    have hzeta : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + z + u)) w :=
      (differentiableAt_riemannZeta hne1).comp w (by fun_prop)
    have hne2 : (1 : ℂ) + w ≠ 1 := by
      intro h; have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith [hw1, ha_pos]
    have hzetaw : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + u)) w :=
      (differentiableAt_riemannZeta hne2).comp w (by fun_prop)
    have hnz : riemannZeta (1 + w) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.add_re, Complex.one_re]; linarith [hw1])
    have hinvw : DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) w := hzetaw.inv hnz
    have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
    have hcpow : DifferentiableAt ℂ (fun u : ℂ => (R : ℂ) ^ (z + u)) w :=
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl hRne)).hasDerivAt.differentiableAt).comp w
        (by fun_prop)
    have hres := ((hf.mul hzeta).mul hinvw).mul hcpow
    have hfun : (((fun u : ℂ => f z u) * (fun u : ℂ => riemannZeta (1 + z + u)))
        * (fun u : ℂ => (riemannZeta (1 + u))⁻¹)) * (fun u : ℂ => (R : ℂ) ^ (z + u))
        = (fun w : ℂ => f z w * riemannZeta (1 + z + w) * (riemannZeta (1 + w))⁻¹
            * (R : ℂ) ^ (z + w)) := by
      funext x; simp only [Pi.mul_apply]
    rw [hfun] at hres
    exact hres
  have hgrowth_H : ∀ w : ℂ, a ≤ w.re → w.re ≤ 1 →
      ‖Hfun w‖ ≤ (B * Cζ * C₁ * R ^ (a + 1)) * (Real.log (|w.im| + 2) + 1) := by
    intro w hw1 hw2
    have hw_ne : w ≠ 0 := by
      intro h; have : w.re = 0 := by rw [h]; simp
      linarith
    have hregw : -(β / Real.log (|w.im| + 2)) ≤ w.re := by
      have : 0 ≤ β / Real.log (|w.im| + 2) :=
        div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg w.im]))
      linarith
    have hf : ‖f z w‖ ≤ B := hbound z w hzreg hzle hregw hw2
    have hzeta : ‖riemannZeta (1 + z + w)‖ ≤ Cζ := by
      apply hCζ
      simp only [Complex.add_re, Complex.one_re, hzre']
      linarith [hw1]
    have hinvw : ‖(riemannZeta (1 + w))⁻¹‖ ≤ C₁ * (Real.log (|w.im| + 2) + 1) :=
      hinvb w hw_ne hregw hw2
    have hcpow : ‖(R : ℂ) ^ (z + w)‖ ≤ R ^ (a + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
      have hre : (z + w).re = a + w.re := by rw [Complex.add_re, hzre']
      rw [hre]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ R) (by linarith)
    have hlogw : 0 ≤ Real.log (|w.im| + 2) + 1 := by
      have : 0 ≤ Real.log (|w.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg w.im])
      linarith
    have hN : ‖Hfun w‖ = ‖f z w‖ * ‖riemannZeta (1 + z + w)‖ * ‖(riemannZeta (1 + w))⁻¹‖
        * ‖(R : ℂ) ^ (z + w)‖ := by
      change ‖f z w * riemannZeta (1 + z + w) * (riemannZeta (1 + w))⁻¹ * (R : ℂ) ^ (z + w)‖
        = ‖f z w‖ * ‖riemannZeta (1 + z + w)‖ * ‖(riemannZeta (1 + w))⁻¹‖ * ‖(R : ℂ) ^ (z + w)‖
      simp only [norm_mul]
    rw [hN]
    calc ‖f z w‖ * ‖riemannZeta (1 + z + w)‖ * ‖(riemannZeta (1 + w))⁻¹‖
            * ‖(R : ℂ) ^ (z + w)‖
        ≤ B * Cζ * (C₁ * (Real.log (|w.im| + 2) + 1)) * R ^ (a + 1) := by
          exact mul_le_mul
            (mul_le_mul (mul_le_mul hf hzeta (norm_nonneg _) hBnn) hinvw (norm_nonneg _)
              (mul_nonneg hBnn hCζpos.le))
            hcpow (norm_nonneg _)
            (mul_nonneg (mul_nonneg hBnn hCζpos.le) (mul_nonneg hC1.le hlogw))
      _ = (B * Cζ * C₁ * R ^ (a + 1)) * (Real.log (|w.im| + 2) + 1) := by ring
  have hpoint : ∀ w : ℂ, Ffun w = K * (Hfun w / w ^ 2) := by
    intro w
    dsimp only [Ffun, Hfun, K]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hC_all : 0 ≤ B * Cζ * C₁ * R ^ (a + 1) := by
    have h1 : 0 ≤ R ^ (a + 1) := le_of_lt (Real.rpow_pos_of_pos hRpos _)
    positivity
  have hmain := vertical_shift_inv_sq_of_log_growth (a := a) (b := 1) ha_pos ha_le_one Hfun
    (B * Cζ * C₁ * R ^ (a + 1)) hC_all hdiff_H hgrowth_H
  have hLHS : (∫ t : ℝ, Ffun ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = K * (∫ t : ℝ, Hfun ((a : ℂ) + (t : ℂ) * Complex.I)
          / (((a : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I) := by
    rw [show (∫ t : ℝ, Ffun ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        = ∫ t : ℝ, K * (Hfun ((a : ℂ) + (t : ℂ) * Complex.I)
            / (((a : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I) by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [hpoint]
      ring,
      MeasureTheory.integral_const_mul]
  have hRHS : (∫ t : ℝ, Ffun ((1 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = K * (∫ t : ℝ, Hfun ((1 : ℂ) + (t : ℂ) * Complex.I)
          / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I) := by
    rw [show (∫ t : ℝ, Ffun ((1 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        = ∫ t : ℝ, K * (Hfun ((1 : ℂ) + (t : ℂ) * Complex.I)
            / (((1 : ℂ) + (t : ℂ) * Complex.I) ^ 2) * Complex.I) by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [hpoint]
      ring,
      MeasureTheory.integral_const_mul]
  have hgoal : (∫ t : ℝ, Ffun ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = ∫ t : ℝ, Ffun ((1 : ℂ) + (t : ℂ) * Complex.I) * Complex.I := by
    rw [hLHS, hRHS, hmain]
    simp only [Complex.ofReal_one]
  rw [ha_def] at hgoal
  dsimp only [Ffun] at hgoal
  exact hgoal

end

end Commons.NumberTheory.Zeta