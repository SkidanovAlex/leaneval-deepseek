import Mathlib
import Submission.Commons.Analysis.Perron.bilinear_perron_bound

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

namespace Commons.Analysis.Complex

/-- The point `c + i t` of the vertical line is nonzero when `c > 0`. -/
lemma perron_sline_ne_zero (c t : ℝ) (hc : 0 < c) :
    (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; rfl
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero] at hre
  linarith

/-- Derivative of `t ↦ c + i t`. -/
lemma hasDerivAt_perron_sline (c t : ℝ) :
    HasDerivAt (fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) Complex.I t := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
    have h : HasDerivAt (id : ℝ → ℝ) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun u : ℝ => u • (1 : ℂ)) ((1 : ℝ) • (1 : ℂ)) t :=
      h.smul_const (1 : ℂ)
    simpa using h2
  have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) (1 * Complex.I) t :=
    h1.mul_const Complex.I
  have h3 : HasDerivAt (fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) (1 * Complex.I) t :=
    h2.const_add (c : ℂ)
  simpa using h3

/-- Integration by parts identity for the second-order Perron kernel. -/
lemma perron_ibp_exp (c x T : ℝ) (hc : 0 < c) (hx : 0 < x) :
    (∫ t in (-T)..T, Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (x : ℂ))
        / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)
      = Complex.I * (Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + (T : ℂ) * Complex.I)
          - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + Complex.log (x : ℂ) * (∫ t in (-T)..T,
            Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (x : ℂ))
              / ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  set L : ℂ := Complex.log (x : ℂ) with hL
  set Aint : ℂ := ∫ t in (-T)..T,
      Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2 with hAint
  set Cint : ℂ := ∫ t in (-T)..T,
      Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) / ((c : ℂ) + (t : ℂ) * Complex.I) with hCint
  set Bdry : ℂ := Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * L)
          / ((c : ℂ) + (T : ℂ) * Complex.I)
        - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * L)
          / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) with hBdry
  have hU : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * L))
      (Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) * (Complex.I * L)) t := by
    intro t
    have hlin : HasDerivAt (fun u : ℝ => ((c : ℂ) + (u : ℂ) * Complex.I) * L) (Complex.I * L) t :=
      (hasDerivAt_perron_sline c t).mul_const L
    exact hlin.cexp
  have hV : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ((c : ℂ) + (u : ℂ) * Complex.I)⁻¹)
      (-(Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) t := by
    intro t
    exact (hasDerivAt_perron_sline c t).inv (perron_sline_ne_zero c t hc)
  have hU'int : IntervalIntegrable
      (fun t : ℝ => Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) * (Complex.I * L)) volume (-T) T := by
    have hd : Continuous (fun t : ℝ => Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) * (Complex.I * L)) := by fun_prop
    exact hd.intervalIntegrable _ _
  have hV'int : IntervalIntegrable
      (fun t : ℝ => -(Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) volume (-T) T := by
    have hw : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have hc2 : Continuous (fun t : ℝ => ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) := hw.pow 2
    have hne : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2 ≠ 0 :=
      fun t => pow_ne_zero 2 (perron_sline_ne_zero c t hc)
    exact (continuous_const.div hc2 hne).intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -T) (b := T)
    (u := fun u : ℝ => Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * L))
    (v := fun u : ℝ => ((c : ℂ) + (u : ℂ) * Complex.I)⁻¹)
    (u' := fun u : ℝ => Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * L) * (Complex.I * L))
    (v' := fun u : ℝ => -(Complex.I) / ((c : ℂ) + (u : ℂ) * Complex.I) ^ 2)
    (fun t _ => hU t) (fun t _ => hV t) hU'int hV'int
  have hconn1 : (∫ t in (-T)..T,
        Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) * (-(Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2))
      = -(Complex.I) * Aint := by
    rw [hAint, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hconn2 : (∫ t in (-T)..T,
        Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * L) * (Complex.I * L) * ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      = (Complex.I * L) * Cint := by
    rw [hCint, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [div_eq_mul_inv]
    ring
  have hbdry : Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * L) * ((c : ℂ) + (T : ℂ) * Complex.I)⁻¹
        - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * L) * ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)⁻¹
      = Bdry := by
    rw [hBdry, div_eq_mul_inv, div_eq_mul_inv]
  rw [hconn1, hconn2, hbdry] at hIBP
  have e1 : Complex.I * (-(Complex.I) * Aint) = Aint := by
    rw [neg_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]
    ring
  have e2 : Complex.I * (-(Complex.I) * Aint) = Complex.I * (Bdry - Complex.I * L * Cint) := by
    rw [hIBP]
  have e3 : Complex.I * (Bdry - Complex.I * L * Cint) = Complex.I * Bdry + L * Cint := by
    rw [mul_sub]
    have hz : Complex.I * (Complex.I * L * Cint) = -(L * Cint) := by
      rw [← mul_assoc, ← mul_assoc, Complex.I_mul_I]; ring
    rw [hz]; ring
  rw [← e1, e2, e3]


/-- Rewrite the `cpow` on the line as an exponential. -/
lemma perron_cpow_line_eq_exp (c x t : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
      = Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  congr 1
  ring

/-- Norm of the exponential factor on the shifted line. -/
lemma norm_cexp_perron_line (c x t : ℝ) (hx : 0 < x) :
    ‖Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (x : ℂ))‖ = x ^ c := by
  rw [← perron_cpow_line_eq_exp c x t hx]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre]

/-- Pointwise rewrite of the second-order kernel integrand. -/
lemma perron_cpow_eq_exp_integral (c x T : ℝ) (hx : 0 < x) :
    (∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2))
      = (∫ t in (-T)..T, Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (x : ℂ))
        / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)) := by
  apply intervalIntegral.integral_congr
  intro t _
  simp only []
  rw [perron_cpow_line_eq_exp c x t hx]

/-- Exact finite truncation of the second-order Perron integral. -/
lemma perron_cpow_finite (c x T : ℝ) (hc : 0 < c) (hx : 0 < x) :
    (∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2))
      = Complex.I * (Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + (T : ℂ) * Complex.I)
          - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + Complex.log (x : ℂ) * ((2 * Real.pi) * stepKern c T x) := by
  rw [perron_cpow_eq_exp_integral c x T hx, perron_ibp_exp c x T hc hx,
    Commons.Analysis.Perron.perron_kernel_integral c T x]

/-- Norm of the second-order kernel. -/
lemma norm_perron_g (c x t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)‖
      = x ^ c / (c ^ 2 + t ^ 2) := by
  have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : ((c : ℂ) + (t : ℂ) * Complex.I).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hden : ‖((c : ℂ) + (t : ℂ) * Complex.I) ^ 2‖ = c ^ 2 + t ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hden, hre]

/-- A convenient dominating function for the second-order kernel. -/
lemma norm_perron_g_le (c x t : ℝ) (hc : 0 < c) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)‖
      ≤ (x ^ c * (1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ := by
  rw [norm_perron_g c x t hx]
  set K : ℝ := (1 + c ^ 2) / c ^ 2 with hK
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hden : 0 < c ^ 2 + t ^ 2 := by positivity
  have hden1 : 0 < 1 + t ^ 2 := by positivity
  have hKpos : 0 < K := by positivity
  have hxc : 0 ≤ x ^ c := (Real.rpow_pos_of_pos hx c).le
  have hineq : 1 + t ^ 2 ≤ K * (c ^ 2 + t ^ 2) := by
    rw [hK, div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith [sq_nonneg t, sq_nonneg c, sq_nonneg (c ^ 2)]
  have h1 : x ^ c / (c ^ 2 + t ^ 2) ≤ (x ^ c * K) / (1 + t ^ 2) := by
    calc x ^ c / (c ^ 2 + t ^ 2) = (K * x ^ c) / (K * (c ^ 2 + t ^ 2)) :=
          (mul_div_mul_left (x ^ c) (c ^ 2 + t ^ 2) hKpos.ne').symm
      _ = (x ^ c * K) / (K * (c ^ 2 + t ^ 2)) := by rw [mul_comm K (x ^ c)]
      _ ≤ (x ^ c * K) / (1 + t ^ 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hxc hKpos.le) hden1 hineq
  calc x ^ c / (c ^ 2 + t ^ 2) ≤ (x ^ c * K) / (1 + t ^ 2) := h1
    _ = (x ^ c * (1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ := by
          rw [hK, div_eq_mul_inv]; ring_nf


/-- The distance from the origin to the point `c + i t` bounds `|t|`. -/
lemma norm_perron_line_ge (c t : ℝ) : |t| ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
  have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : ((c : ℂ) + (t : ℂ) * Complex.I).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hsq : c ^ 2 + t ^ 2 = ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  have hle : t ^ 2 ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
    rw [← hsq]; nlinarith [sq_nonneg c]
  calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ Real.sqrt (‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := Real.sqrt_sq (norm_nonneg _)

/-- The boundary term of the integration by parts tends to zero. -/
lemma perron_bdry_tendsto (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Filter.Tendsto (fun T : ℝ => Complex.I *
        (Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + (T : ℂ) * Complex.I)
          - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
      Filter.atTop (nhds 0) := by
  have hpos : ∀ᶠ T : ℝ in Filter.atTop, (0 : ℝ) < T := Filter.eventually_gt_atTop 0
  have hxc : 0 ≤ x ^ c := (Real.rpow_pos_of_pos hx c).le
  have hbound1 : ∀ T : ℝ, 0 < T →
      ‖Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
          / ((c : ℂ) + (T : ℂ) * Complex.I)‖ ≤ x ^ c * T⁻¹ := by
    intro T hT
    rw [norm_div, norm_cexp_perron_line c x T hx]
    have hle : T ≤ ‖(c : ℂ) + (T : ℂ) * Complex.I‖ :=
      le_of_eq_of_le (abs_of_pos hT).symm (norm_perron_line_ge c T)
    calc x ^ c / ‖(c : ℂ) + (T : ℂ) * Complex.I‖ ≤ x ^ c / T :=
          div_le_div_of_nonneg_left hxc hT hle
      _ = x ^ c * T⁻¹ := by rw [div_eq_mul_inv]
  have hbound2 : ∀ T : ℝ, 0 < T →
      ‖Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
          / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ x ^ c * T⁻¹ := by
    intro T hT
    rw [norm_div, norm_cexp_perron_line c x (-T) hx]
    have hle : T ≤ ‖(c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I‖ :=
      le_of_eq_of_le (show T = |(-T)| by rw [abs_neg, abs_of_pos hT])
        (norm_perron_line_ge c (-T))
    calc x ^ c / ‖(c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I‖ ≤ x ^ c / T :=
          div_le_div_of_nonneg_left hxc hT hle
      _ = x ^ c * T⁻¹ := by rw [div_eq_mul_inv]
  have hlim : Filter.Tendsto (fun T : ℝ => x ^ c * T⁻¹) Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.const_mul (x ^ c) tendsto_inv_atTop_zero :
      Filter.Tendsto (fun T : ℝ => x ^ c * T⁻¹) Filter.atTop (nhds (x ^ c * 0)))
  have h1 : Filter.Tendsto (fun T : ℝ =>
      Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
        / ((c : ℂ) + (T : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _))
      (by filter_upwards [hpos] with T hT; exact hbound1 T hT) hlim
  have h2 : Filter.Tendsto (fun T : ℝ =>
      Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
        / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _))
      (by filter_upwards [hpos] with T hT; exact hbound2 T hT) hlim
  have hmain : Filter.Tendsto (fun T : ℝ =>
      (Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + (T : ℂ) * Complex.I)
          - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))) Filter.atTop (nhds 0) := by
    simpa using h1.sub h2
  simpa using hmain.const_mul Complex.I

/-- The Perron step kernel converges to the indicator of `(1, ∞)`. -/
lemma perron_stepKern_tendsto (c x : ℝ) (hc : 0 < c) (hx : 0 < x) (hx1 : x ≠ 1) :
    Filter.Tendsto (fun T : ℝ => stepKern c T x) Filter.atTop
      (nhds (if (1 : ℝ) < x then (1 : ℂ) else 0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlog : 0 < |Real.log x| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hx hx1)
  have hden : Filter.Tendsto (fun T : ℝ => T * |Real.log x|) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hlog (tendsto_id : Filter.Tendsto (id : ℝ → ℝ) Filter.atTop Filter.atTop)
  have hrec : Filter.Tendsto (fun T : ℝ => 1 / (T * |Real.log x|)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hmin : Filter.Tendsto (fun T : ℝ => min 1 (1 / (T * |Real.log x|))) Filter.atTop
      (nhds (min 1 0)) := tendsto_const_nhds.min hrec
  have hlim : Filter.Tendsto
      (fun T : ℝ => (32 / (2 * Real.pi)) * x ^ c * min 1 (1 / (T * |Real.log x|)))
      Filter.atTop (nhds 0) := by
    simpa using hmin.const_mul ((32 / (2 * Real.pi)) * x ^ c)
  refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  exact perronStep_deviation_pos c T x hc hT hx hx1

/-- The second-order Perron integrand, in exponential form. -/
noncomputable def perronK2 (c x t : ℝ) : ℂ :=
  Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (x : ℂ))
    / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)

/-- Exact finite truncation of the exponential-form second-order Perron integral. -/
lemma perron_exp_finite (c x T : ℝ) (hc : 0 < c) (hx : 0 < x) :
    (∫ t in (-T)..T, perronK2 c x t)
      = Complex.I * (Complex.exp (((c : ℂ) + (T : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + (T : ℂ) * Complex.I)
          - Complex.exp (((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) * Complex.log (x : ℂ))
            / ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + Complex.log (x : ℂ) * ((2 * Real.pi) * stepKern c T x) := by
  have h := perron_ibp_exp c x T hc hx
  simp only [perronK2]
  rw [h, Commons.Analysis.Perron.perron_kernel_integral c T x]

/-- Limit of the truncated second-order Perron integral. -/
lemma perron_interval_tendsto (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Filter.Tendsto (fun T : ℝ => ∫ t in (-T)..T, perronK2 c x t) Filter.atTop
      (nhds (Complex.log (x : ℂ) * (2 * Real.pi * (if (1 : ℝ) < x then (1 : ℂ) else 0)))) := by
  have hbd := perron_bdry_tendsto c x hc hx
  have hstep : Filter.Tendsto
      (fun T : ℝ => Complex.log (x : ℂ) * (2 * Real.pi * stepKern c T x)) Filter.atTop
      (nhds (Complex.log (x : ℂ) * (2 * Real.pi * (if (1 : ℝ) < x then (1 : ℂ) else 0)))) := by
    by_cases hx1 : x = 1
    · have h1' : Complex.log (x : ℂ) = 0 := by rw [hx1, Complex.ofReal_one, Complex.log_one]
      have h2' : (if (1 : ℝ) < x then (1 : ℂ) else 0) = 0 :=
        if_neg (by rw [hx1]; exact lt_irrefl 1)
      rw [h1', h2']
      simp only [zero_mul]
      exact tendsto_const_nhds
    · exact ((perron_stepKern_tendsto c x hc hx hx1).const_mul (2 * (Real.pi : ℂ))).const_mul
        (Complex.log (x : ℂ))
  have hsum := hbd.add hstep
  refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T _
  rw [perron_exp_finite c x T hc hx]
  simp only [Complex.ofReal_neg, neg_mul]

/-- The truncated second-order Perron integral converges to the full integral. -/
lemma perron_integral_tendsto (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Filter.Tendsto (fun T : ℝ => ∫ t in (-T)..T, perronK2 c x t) Filter.atTop
      (nhds (∫ t : ℝ, perronK2 c x t)) := by
  set C : ℝ := x ^ c * (1 + c ^ 2) / c ^ 2 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hbound : ∀ t : ℝ, ‖perronK2 c x t‖ ≤ C * (1 + t ^ 2)⁻¹ := by
    intro t
    simp only [perronK2]
    rw [← perron_cpow_line_eq_exp c x t hx, hC]
    exact norm_perron_g_le c x t hc hx
  have hgcont : Continuous (perronK2 c x) := by
    change Continuous (fun t : ℝ => Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I)
      * Complex.log (x : ℂ)) / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2))
    refine Continuous.div (by fun_prop) (by fun_prop) (fun t => ?_)
    exact pow_ne_zero 2 (perron_sline_ne_zero c t hc)
  have hmeas : ∀ᶠ T : ℝ in Filter.atTop,
      AEStronglyMeasurable ((Set.Ioc (-T) T).indicator (perronK2 c x)) volume :=
    Filter.Eventually.of_forall (fun T =>
      (hgcont.aestronglyMeasurable).indicator measurableSet_Ioc)
  have hdom : ∀ᶠ T : ℝ in Filter.atTop,
      ∀ᵐ t ∂volume, ‖(Set.Ioc (-T) T).indicator (perronK2 c x) t‖ ≤ C * (1 + t ^ 2)⁻¹ :=
    Filter.Eventually.of_forall (fun T => Filter.Eventually.of_forall (fun t => by
      calc ‖(Set.Ioc (-T) T).indicator (perronK2 c x) t‖
          ≤ ‖(Set.univ).indicator (perronK2 c x) t‖ :=
            norm_indicator_le_of_subset (Set.subset_univ _) (perronK2 c x) t
        _ ≤ C * (1 + t ^ 2)⁻¹ := by simpa using hbound t))
  have hint : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul C
  have hpt : ∀ᵐ t ∂volume,
      Filter.Tendsto (fun T : ℝ => (Set.Ioc (-T) T).indicator (perronK2 c x) t) Filter.atTop
        (nhds (perronK2 c x t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop |t|] with T hT
    rw [Set.indicator_of_mem (show t ∈ Set.Ioc (-T) T from by
      simp only [Set.mem_Ioc]
      constructor <;> linarith [neg_abs_le t, le_abs_self t, hT])]
  have key := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := Filter.atTop)
      (F := fun T : ℝ => fun t : ℝ => (Set.Ioc (-T) T).indicator (perronK2 c x) t)
      (f := perronK2 c x) (bound := fun t : ℝ => C * (1 + t ^ 2)⁻¹)
      hmeas hdom hint hpt
  refine Filter.Tendsto.congr' ?_ key
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  have hle : -T ≤ T := by linarith
  rw [MeasureTheory.integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hle]

/-- Cancellation of the `2π` normalising constant. -/
lemma perron_scale_cancel (l s : ℂ) :
    (1 / (2 * (Real.pi : ℂ))) * (l * (2 * (Real.pi : ℂ) * s)) = l * s := by
  have hpi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  field_simp

theorem perron_log_identity {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)
      = if 1 < x then (Real.log x : ℂ) else 0 := by
  have hval : (∫ t : ℝ, perronK2 c x t)
      = Complex.log (x : ℂ) * (2 * Real.pi * (if (1 : ℝ) < x then (1 : ℂ) else 0)) :=
    tendsto_nhds_unique (perron_integral_tendsto c x hc hx) (perron_interval_tendsto c x hc hx)
  have hbridge : (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)) = (∫ t : ℝ, perronK2 c x t) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simp only [perronK2]
    rw [perron_cpow_line_eq_exp c x t hx]
  rw [hbridge, hval]
  by_cases h1x : (1 : ℝ) < x
  · have hsv : (if (1 : ℝ) < x then (1 : ℂ) else 0) = 1 := if_pos h1x
    have hLx : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
    rw [hsv, hLx, if_pos h1x]
    rw [perron_scale_cancel (Real.log x : ℂ) 1, mul_one]
  · have hsv : (if (1 : ℝ) < x then (1 : ℂ) else 0) = 0 := if_neg h1x
    rw [hsv, if_neg h1x]
    simp


end Commons.Analysis.Complex
