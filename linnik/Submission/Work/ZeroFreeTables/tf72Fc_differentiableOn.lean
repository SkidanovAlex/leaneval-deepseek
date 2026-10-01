import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

noncomputable section

namespace Work.ZeroFreeTables

/-- The polynomial that agrees with `tf72f lam` on `[0, 2/lam]`
(see `tf72f_eq_poly`).  It is used as an everywhere-continuous model of the
test function, which makes differentiating under the integral sign in the
Laplace transform `tf72Fc` straightforward. -/
private def tf72poly (lam t : ℝ) : ℝ :=
  (lam / 30) * (2 - lam * t) ^ 3 * (4 + 6 * lam * t + lam ^ 2 * t ^ 2)

/-- `tf72Fc lam` differs from the Laplace transform of the *polynomial*
`tf72poly lam` only on the interval of integration `uIoc 0 (2/lam)`, where the
two agree pointwise. -/
private lemma tf72Fc_eq_integral_poly (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    tf72Fc lam z = ∫ t in (0 : ℝ)..(2 / lam),
      Complex.exp (-(z * (t : ℂ))) * ((tf72poly lam t : ℝ) : ℂ) := by
  unfold tf72Fc
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with t ht
  have hK : (0 : ℝ) < 2 / lam := by positivity
  rw [Set.uIoc_of_le hK.le] at ht
  rw [tf72f_eq_poly lam hlam t ⟨le_of_lt ht.1, ht.2⟩]
  simp only [tf72poly]

/-- The Laplace transform of the polynomial model `tf72poly lam` over `[0, 2/lam]`
is entire; this is the heart of the differentiability of `tf72Fc`. -/
private lemma differentiable_integral_exp_poly (lam : ℝ) (hlam : 0 < lam) :
    Differentiable ℂ (fun z : ℂ => ∫ t in (0 : ℝ)..(2 / lam),
      Complex.exp (-(z * (t : ℂ))) * ((tf72poly lam t : ℝ) : ℂ)) := by
  intro z₀
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => Complex.exp (-(z * (t : ℂ))) * ((tf72poly lam t : ℝ) : ℂ))
    (F' := fun z t => Complex.exp (-(z * (t : ℂ))) * (-(t : ℂ)) * ((tf72poly lam t : ℝ) : ℂ))
    (bound := fun t => (Real.exp ((‖z₀‖ + 1) * (2 / lam)) * (2 / lam)) * |tf72poly lam t|)
    (x₀ := z₀) (s := Metric.ball z₀ 1) (a := 0) (b := 2 / lam)
    (Metric.ball_mem_nhds z₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt
  · -- a.e. strong measurability of the integrand, for `z` near `z₀`
    filter_upwards with x
    apply Measurable.aestronglyMeasurable
    unfold tf72poly; fun_prop
  · -- integrability of the integrand at `z₀`
    have hc : Continuous (fun t : ℝ =>
        Complex.exp (-(z₀ * (t : ℂ))) * ((tf72poly lam t : ℝ) : ℂ)) := by
      unfold tf72poly; fun_prop
    exact hc.intervalIntegrable 0 (2 / lam)
  · -- a.e. strong measurability of the differentiated integrand
    apply Measurable.aestronglyMeasurable
    unfold tf72poly; fun_prop
  · -- uniform bound on the differentiated integrand
    filter_upwards with t ht x hx
    have hK : (0 : ℝ) < 2 / lam := by positivity
    rw [Set.uIoc_of_le hK.le] at ht
    have ht1 : 0 < t := ht.1
    have ht2 : t ≤ 2 / lam := ht.2
    have hx1 : ‖x‖ < ‖z₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h3 : ‖x‖ ≤ ‖x - z₀‖ + ‖z₀‖ := by
        have := norm_add_le (x - z₀) z₀
        simpa using this
      linarith
    simp only [norm_mul, Complex.norm_exp, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hstep : Real.exp (-(x * (t : ℂ))).re ≤ Real.exp ((‖z₀‖ + 1) * (2 / lam)) := by
      apply Real.exp_le_exp.mpr
      have hre : (-(x * (t : ℂ))).re = -(x * (t : ℂ)).re := Complex.neg_re _
      rw [hre]
      have h2 : -(x * (t : ℂ)).re ≤ ‖x * (t : ℂ)‖ :=
        le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h2
      have htabs : |t| ≤ 2 / lam := by rw [abs_of_pos ht1]; exact ht2
      nlinarith [norm_nonneg x, abs_nonneg t]
    have htabs : |t| ≤ 2 / lam := by rw [abs_of_pos ht1]; exact ht2
    have h4 : Real.exp (-(x * (t : ℂ))).re * |t| ≤
        Real.exp ((‖z₀‖ + 1) * (2 / lam)) * (2 / lam) :=
      mul_le_mul hstep htabs (abs_nonneg t) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
  · -- integrability of the bound
    have hc : Continuous (fun t : ℝ =>
        (Real.exp ((‖z₀‖ + 1) * (2 / lam)) * (2 / lam)) * |tf72poly lam t|) := by
      unfold tf72poly; fun_prop
    exact hc.intervalIntegrable 0 (2 / lam)
  · -- differentiability of the integrand in `z`
    filter_upwards with t ht x hx
    have h1 : HasDerivAt (fun z : ℂ => z * (t : ℂ)) (t : ℂ) x := by
      simpa using (hasDerivAt_id x).mul_const (t : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => -(z * (t : ℂ))) (-(t : ℂ)) x := h1.neg
    have h3 := h2.cexp
    simpa using h3.mul_const ((tf72poly lam t : ℝ) : ℂ)

theorem tf72Fc_differentiableOn (lam : ℝ) (hlam : 0 < lam) :
    DifferentiableOn ℂ (Work.ZeroFreeTables.tf72Fc lam) {z : ℂ | 0 ≤ z.re} := by
  rw [show tf72Fc lam = (fun z : ℂ => ∫ t in (0 : ℝ)..(2 / lam),
      Complex.exp (-(z * (t : ℂ))) * ((tf72poly lam t : ℝ) : ℂ)) from
    funext (tf72Fc_eq_integral_poly lam hlam)]
  exact (differentiable_integral_exp_poly lam hlam).differentiableOn

end Work.ZeroFreeTables
